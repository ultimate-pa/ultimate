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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.NestedArrayStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.QuantifierSequence;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.QuantifierSequence.QuantifiedVariables;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.pqe.XnfDer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class ArrayQuantifierEliminationMain {

	private final ManagedScript mMgdScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private final int mRecursiveCallCounter = -1;
	private final Script mScript;
	private Set<TermVariable> mEliminatees;

	public ArrayQuantifierEliminationMain(final ManagedScript mgdScript, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique) {
		super();
		mMgdScript = mgdScript;
		mScript = mMgdScript.getScript();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mEliminatees = new HashSet<TermVariable>();
	}

	/*
	 * Main Method of the Array Quantifier Elimination For each quantified Array
	 * variable - it eliminates one Store Terms - it eliminates all Select Terms -
	 * it checks the Input Term for Inconsistents Input/Output: is an
	 * EliminationTask
	 *
	 * TODO: - test for multiple Stores - Store over Store - collect and use Index
	 * Information - implement it for forall and disjunction - make sure it works
	 * for all possible Formula(dnf cnf) no mather how Deep
	 */
	public EliminationTask elimAllRec(EliminationTask eTask) {
		mEliminatees.addAll(eTask.getEliminatees());

		System.out.print("New Array Elimination USED\n");
		EliminationTask result = eTask;
		System.out.print("Zu eliminieren: " + eTask.getEliminatees() + "\n");
		System.out.print("Term: " + eTask.getTerm() + "\n");
		if (eTask.getTerm() instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) eTask.getTerm();

			// TODO Count Store/Select Axioms?

			final ThreeValuedEquivalenceRelation tVER = calcThreeValuedEquiRel(result); // TODO use in all Index
																						// comparisons
			if (SmtUtils.isFunctionApplication(eTask.getTerm(), "and") && (eTask.getQuantifier() == 0)) {
				// TODO QuantifierUtils nutzen
				if ((tVER.isInconsistent()) && (!tVER.getAllElements().isEmpty())) {
					result = new EliminationTask(result.getQuantifier(), result.getEliminatees(),
							mScript.term("false"));
				}
			} else if (SmtUtils.isFunctionApplication(eTask.getTerm(), "or") && (eTask.getQuantifier() == 1)) {
				if ((tVER.isTautological()) && (!tVER.getAllElements().isEmpty())) {
					result = new EliminationTask(result.getQuantifier(), result.getEliminatees(), mScript.term("true"));
				}
			}
			Term taskTerm = result.getTerm();

			// TODO ADD NEW QUANTIFIERS WIP TODO Fehler in Butan!
			// MultiDimArrayHandler mDAH = new
			// MultiDimArrayHandler(mMgdScript,mServices,mSimplificationTechnique,eTask.getEliminatees());
			// taskTerm = mDAH.multiDimArrayHandlerSelect(taskTerm);
			// mDAH.buildNewElimTask(eTask.getQuantifier(), taskTerm);

			taskTerm = storeOverStore(taskTerm, tVER);
			taskTerm = selectOverStore(taskTerm, tVER);
			System.out.print("!Term after SOS: " + taskTerm.toStringDirect() + "\n");
				
			result = new EliminationTask(eTask.getQuantifier(), mEliminatees, taskTerm);		
			result = elim1StoreQuantifier(result);
			Term simpleTerm = SmtUtils.simplify(mMgdScript, result.getTerm(), mServices, mSimplificationTechnique);
			result = new EliminationTask(eTask.getQuantifier(), mEliminatees, simpleTerm);	
			
			// "occurrence-based store elimination": occStoreElim
/*
			 result = occStoreElim(result); // With Index SET
			
			 result = distributivity(result, appterm.getFunction().getName()); //TODO nur
			 // f�r Array Quantoren
			 //
			 EliminationTask newETask = result;
			 int counter2 = 0;
			 for (TermVariable qArray : newETask.getEliminatees()) {
			 newETask = elimMultiSelectNaiv(newETask.getTerm(), qArray,
			 newETask.getQuantifier(), counter2);
			 counter2 += 1;
			 }
			 result = new EliminationTask(newETask.getQuantifier(),
			 newETask.getEliminatees(), newETask.getTerm());
*/
		}
		assert !Arrays.asList(result.getTerm().getFreeVars())
				.contains(eTask.getEliminatees()) : "var is	 still there";

		return result;

	}

	/*
	 * Eliminates Array Equalitys. There for we wont add new Index Quantifiers.
	 * Instead we'll eliminate them directly by using "collectArrayIndices"
	 *
	 * Only Use this in Combination with Store elimiation. To Ensure
	 * Correctness(Yemen Saudiarabia tests). Warning! We wont be able to use DER on
	 * these Equalitys afterwards.
	 *
	 */

	private Term eliminateEQ(final Term term, final Set<TermVariable> eliminatees) {
		Term noeqterm = term;
		collectArrayIndices(term);
		// find Array EQ DEQ in term.
		final ApplicationTermFinder atfeq = new ApplicationTermFinder("=", false);
		final Set<ApplicationTerm> eqSet = atfeq.findMatchingSubterms(term);
		for (final ApplicationTerm appterm : eqSet) {
			if (appterm.getParameters().length == 2) {
				if ((SmtUtils.isBasicArrayTerm(appterm.getParameters()[0]))
						&& (SmtUtils.isBasicArrayTerm(appterm.getParameters()[0]))) {
					// don't eliminate Quantified Array Equalities for DER
					if ((!eliminatees.contains(appterm.getParameters()[0]))
							&& (!eliminatees.contains(appterm.getParameters()[1]))) {
						// appterm ist Array EQ.
						final Set<Term> indexSet = collectArrayIndices(term); // TODO keine COde Duplikation
						Term newEquailty = mScript.term("true"); // neutral Element for Conjunction
						for (final Term indexvar1 : indexSet) {
							for (final Term indexvar2 : indexSet) {
								if (indexvar1 == indexvar2) {
									// Build newterm for EQ.
									final Term select1 = SmtUtils.select(mScript, appterm.getParameters()[0],
											indexvar1);
									final Term select2 = SmtUtils.select(mScript, appterm.getParameters()[1],
											indexvar2);
									final Term newEquailtyPart = SmtUtils.binaryEquality(mScript, select1, select2);
									newEquailty = SmtUtils.and(mScript, newEquailtyPart, newEquailty);
								}

							}
						}
						// Substitude newterms
						final Map<Term, Term> submap = new HashMap();
						submap.put(appterm, newEquailty);
						final Substitution sub = new Substitution(mMgdScript, submap);
						submap.clear();
						noeqterm = sub.transform(noeqterm);
					}

				}
			}
		}
		System.out.print("DEBUG EqElim: " + noeqterm.toStringDirect() + "\n");
		return noeqterm;
	}

	/*
	 *
	 * TODO Store over Store rekursiv. Nur eliminieren, wenn Indexe Gleich.
	 * ThreeValueEq nutzen
	 */
	private Term storeOverStore(final Term term, final ThreeValuedEquivalenceRelation tVER) {
		final MultiDimensionalStore mds = new MultiDimensionalStore(term);
		final List<MultiDimensionalStore> Storeterms = mds.extractArrayStoresShallow(term);
		for (final MultiDimensionalStore storeOuter : Storeterms) {

			NestedArrayStore nas = NestedArrayStore.convert(storeOuter.getStoreTerm());
			if (nas.getIndices().size() > 1) {

				// for (int store = 0; store < nas.getIndices().size(); store++) {
				if (mEliminatees.contains(nas.getArray())) {

					if (testIndexVarTerm(nas.getIndices().get(0), nas.getIndices().get(1), tVER)) {
						if (tVER.getEqualityStatus(nas.getIndices().get(0),
								nas.getIndices().get(1)) == (EqualityStatus.EQUAL)) {

							final Term newStore = SmtUtils.store(mScript, nas.getArray(), nas.getIndices().get(0),
									nas.getValues().get(1));

							// Substitude newStore
							final Substitution sub = new Substitution(mMgdScript,
									Collections.singletonMap(storeOuter.getStoreTerm(), newStore));
							final Term noSOSterm = sub.transform(term);

							return storeOverStore(noSOSterm, tVER);
						}
					}
				}
				TermVariable newarrayvar = mMgdScript.constructFreshTermVariable("a_sos",
						storeOuter.getArray().getSort());
				Term innerStore = SmtUtils.store(mScript, nas.getArray(), nas.getIndices().get(0),
						nas.getValues().get(0));
				final Substitution sub = new Substitution(mMgdScript,
						Collections.singletonMap(innerStore, newarrayvar));

				Term noSOSterm = sub.transform(term);
				mEliminatees.add(newarrayvar);
				// Index comparison Equality
				Term factorisedStore = SmtUtils.binaryEquality(mScript, newarrayvar, innerStore);
				Term newTerm = SmtUtils.and(mScript, factorisedStore, noSOSterm);

				return storeOverStore(newTerm, tVER);

			}
			// }

		}

		return term;

	}

	/*
	 * Rekursion Gets all Select Terms. If the Array is not inestance of
	 * VariableTerm, its a Store Term. Then we Replace term with newterm, using the
	 * following Rule:
	 *
	 * TODO Optimierung Index gleichheit TODO No recursion, while instead TODO
	 * Select Over Store Over Store...
	 *
	 */
	private Term selectOverStore(final Term term, final ThreeValuedEquivalenceRelation tVER) {
		final MultiDimensionalSelect mds = new MultiDimensionalSelect(term);
		final List<MultiDimensionalSelect> Selectterms = mds.extractSelectDeep(term, false);
		for (final MultiDimensionalSelect select : Selectterms) {
			// if Array is BasicArray, its no SelectOverStore
			if (!SmtUtils.isBasicArrayTerm(select.getArray())) {
				final MultiDimensionalStore innerStore = new MultiDimensionalStore(select.getArray());
				if ((SmtUtils.isBasicArrayTerm(innerStore.getArray()))) {
					if (mEliminatees.contains(innerStore.getArray())) {
						// 2 Substitutions for IndexEQ and IndexNEQ
						final Substitution sub = new Substitution(mMgdScript,
								Collections.singletonMap(select.getSelectTerm(), innerStore.getValue()));
						final Term subtermlhs = sub.transform(term);
						final Substitution sub2 = new Substitution(mMgdScript,
								Collections.singletonMap(select.getSelectTerm(),
										SmtUtils.select(mScript, innerStore.getArray(), select.getIndex().get(0))));
						final Term subtermrhs = sub2.transform(term);

						// Index comparison Equality
						Term indexeq = SmtUtils.binaryEquality(mScript, innerStore.getIndex().get(0),
								select.getIndex().get(0));
						// Index comparison DisEquality
						Term indexnoteq = SmtUtils.not(mScript, SmtUtils.binaryEquality(mScript,
								innerStore.getIndex().get(0), select.getIndex().get(0)));
						if (testIndexVarTerm(innerStore.getIndex().get(0), select.getIndex().get(0), tVER)) {

							if (tVER.getDisequalities().containsPair(innerStore.getIndex().get(0),
									select.getIndex().get(0))) {
								indexeq = mScript.term("false");
								indexnoteq = mScript.term("true");

							} else if (tVER.getEqualityStatus(innerStore.getIndex().get(0), select.getIndex().get(0))
									.compareTo(EqualityStatus.EQUAL) == 0) {
								indexeq = mScript.term("true");
								indexnoteq = mScript.term("false");
							}
						}

						final Term lhs = SmtUtils.and(mScript, indexeq, subtermlhs);
						final Term rhs = SmtUtils.and(mScript, indexnoteq, subtermrhs);
						Term newterm = SmtUtils.or(mScript, lhs, rhs);						
						newterm = SmtUtils.simplify(mMgdScript, newterm, mServices, mSimplificationTechnique);
						return newterm;
					}
				} else if (innerStore != null) {
					// Sub Store Over Store
					final Substitution sub = new Substitution(mMgdScript, Collections
							.singletonMap(innerStore.getStoreTerm(), storeOverStore(innerStore.getStoreTerm(), tVER)));
					final Term elimSOS = sub.transform(term);
					Term terma =  storeOverStore(elimSOS, tVER);
					return selectOverStore(terma, tVER);
				}
			}
		}

		return term;
	}

	private boolean testIndexVarTerm(final Term index1, final Term index2, ThreeValuedEquivalenceRelation tVER) {
		if (tVER.getAllElements().contains(index1)) {
			if (tVER.getAllElements().contains(index2)) {
				if (!(index1 instanceof ConstantTerm)) {
					if (!(index2 instanceof ConstantTerm)) {
						return true;
					}
				}
			}
		}
		return false;
	}

	/*
	 * Collects all Array Indices of a Term. Can be used to eliminate Forall
	 * Quantifier, iterating over indices.
	 *
	 * Input: Term with Select and Store operations Output: a Set of Terms,
	 * containing all Indices of all Store and Select terms
	 *
	 * TODO: - Check if collecting Store Indices is correct/usefull
	 */

	private Set<Term> collectArrayIndices(final Term term) {

		final MultiDimensionalSelect mdSelect = new MultiDimensionalSelect(term);
		final List<MultiDimensionalSelect> mdSelectDeep = mdSelect.extractSelectDeep(term, false);
		final MultiDimensionalStore mdStore = new MultiDimensionalStore(term);
		final List<MultiDimensionalStore> mdStoreDeep = mdStore.extractArrayStoresDeep(term);
		final Set<Term> indexSet = new HashSet<Term>();
		for (final MultiDimensionalSelect mds : mdSelectDeep) {
			indexSet.add(mds.getIndex().get(0));
		}
		for (final MultiDimensionalStore mds : mdStoreDeep) {
			indexSet.add(mds.getIndex().get(0));
		}
		return indexSet;
	}

	/*
	 * Eliminates one Store operation (Store a i v) with an quantified Array "a". -
	 * It replaces the Store term (Store a i v) with a new Exists quantified Array
	 * Variable a_new and adds the Conjunct "a_new = (Store a i v)".
	 *
	 * - We collect all Indices of the Input Term - We Build a new SubTerm - We
	 * eliminate the new Index Forall Quantifier with the collected Indices. - We
	 * Replace "a_new = (Store a i v)" with the new SubTerm.
	 *
	 * Returns an EliminationTask. Its Term has no more Store Operation and no new
	 * Quantifiers.
	 *
	 *
	 */
	private EliminationTask occStoreElim(final EliminationTask eTask) {
		final MultiDimensionalStore mds = new MultiDimensionalStore(eTask.getTerm());
		final List<MultiDimensionalStore> storeterms = mds.extractArrayStoresDeep(eTask.getTerm());
		int counter = 0;
		Term newterm = eTask.getTerm();
		final Set<TermVariable> neweliminatees2 = new HashSet<TermVariable>();
		// for store new exists array a1 quantifier
		for (final MultiDimensionalStore term : storeterms) {
			if (eTask.getEliminatees().contains(term.getArray())) {

				final TermVariable newarrayvar = mScript.variable("a_new_" + counter, term.getArray().getSort());
				final Set<TermVariable> neweliminatees = new HashSet<TermVariable>();
				neweliminatees.add(newarrayvar);
				// Substitute Store term with new Exist quantified Array Variable a_new

				Substitution sub = new Substitution(mMgdScript,
						Collections.singletonMap(term.getStoreTerm(), newarrayvar));

				newterm = sub.transform(newterm);
				// Add conjunct a1 = (eliminated store term)
				final Term eqterm = SmtUtils.binaryEquality(mScript, newarrayvar, term.getStoreTerm());
				newterm = SmtUtils.and(mScript, newterm, eqterm);
				final TermVariable newindexvar = mScript.variable("j_" + counter, SmtSortUtils.getIntSort(mMgdScript));
				neweliminatees2.add(newindexvar);
				// Build new Term forall Indices of indexSet
				Term elimForall = mScript.term("true"); // neutral Element for Conjunction
				final Set<Term> indexSet = collectArrayIndices(eTask.getTerm()); // TODO keine COde Duplikation
				indexSet.remove(newindexvar);
				for (final Term indexvar : indexSet) {
					// Term 1: ((i != j) => (a_new[i] = a[i]))
					final Term indexnoteq = SmtUtils.not(mScript,
							SmtUtils.binaryEquality(mScript, indexvar, term.getStoreTerm().getParameters()[1]));
					final Term arrayeq = SmtUtils.binaryEquality(mScript,
							SmtUtils.select(mScript, newarrayvar, indexvar),
							SmtUtils.select(mScript, term.getArray(), indexvar));
					final Term elimtermlhs = SmtUtils.implies(mScript, indexnoteq, arrayeq);
					// Term 2: ((i = j) => (a_new[i] = v))
					final Term indexeq = SmtUtils.binaryEquality(mScript, indexvar,
							term.getStoreTerm().getParameters()[1]);
					final Term selectvalue = SmtUtils.binaryEquality(mScript,
							SmtUtils.select(mScript, newarrayvar, indexvar), term.getValue());
					final Term elimtermrhs = SmtUtils.implies(mScript, indexeq, selectvalue);
					// Term 3: Term 1 AND Term 2
					final Term elimterm = SmtUtils.and(mScript, elimtermlhs, elimtermrhs);
					// elimForall AND Term 3
					elimForall = SmtUtils.and(mScript, elimForall, elimterm);

				}
				// Substitute Store term equality with the new Term "elimForall"
				sub = new Substitution(mMgdScript, Collections.singletonMap(eqterm, elimForall));
				newterm = sub.transform(newterm);
				counter += 1;
				// DER on a_new. To eliminate the new Exist Quantifier: "Exists a_new"
				final XnfDer xnfDer = new XnfDer(mMgdScript, mServices);
				final Term[] oldParams = QuantifierUtils.getXjunctsOuter(0, newterm);
				final Term[] newParams = new Term[oldParams.length];
				for (int i = 0; i < oldParams.length; i++) {
					final Set<TermVariable> eliminateesDER = new HashSet<>(neweliminatees);
					final Term[] oldAtoms = QuantifierUtils.getXjunctsInner(0, oldParams[i]);
					newParams[i] = QuantifierUtils.applyDualFiniteConnective(mScript, 0,
							Arrays.asList(xnfDer.tryToEliminate(0, oldAtoms, eliminateesDER)));
				}

				newterm = QuantifierUtils.applyCorrespondingFiniteConnective(mScript, 0, newParams);
			}
		}
		newterm = eliminateEQ(newterm, eTask.getEliminatees()); // Make Sure we don't Loose Equality
																// Informations(Partial Array Equalities)
		final EliminationTask noStoreTerm = new EliminationTask(eTask.getQuantifier(), eTask.getEliminatees(), newterm);
		return noStoreTerm;
	}

	/*
	 * Stores all Equalities / Disequalities of an conjunction and Checks for
	 * Inconsistens. Equalitys in the Input Formula are always valid. Equalitys only
	 * count in one Disjunction
	 */

	private ThreeValuedEquivalenceRelation calcThreeValuedEquiRel(final EliminationTask eTask) {
		final ApplicationTerm appterm = (ApplicationTerm) eTask.getTerm();
		final ThreeValuedEquivalenceRelation<Term> tVER = new ThreeValuedEquivalenceRelation<Term>();
		if (SmtUtils.isFunctionApplication(eTask.getTerm(), "and")) {
			for (final Term term : appterm.getParameters()) {
				if (term.getSort().getName().equals("Bool")) {
					final ApplicationTerm boolterm = (ApplicationTerm) term;
					if (boolterm.getFunction().getName().equals("=")) {
						// Add Equality
						tVER.addElement(boolterm.getParameters()[0]);
						tVER.addElement(boolterm.getParameters()[1]);
						tVER.reportEquality(boolterm.getParameters()[0], boolterm.getParameters()[1]);

					} else if (boolterm.getFunction().getName().equals("not")) {
						// Add Disequality
						final ApplicationTerm eqterm = (ApplicationTerm) boolterm.getParameters()[0];
						tVER.addElement(eqterm.getParameters()[0]);
						tVER.addElement(eqterm.getParameters()[1]);
						tVER.reportDisequality(eqterm.getParameters()[0], eqterm.getParameters()[1]);
					}
				}
			}
		}
		return tVER;
	}

	/*
	 * Distributivity
	 */

	private EliminationTask distributivity(final EliminationTask eTask, final String fun) {
		if (((fun.equals("or") && (eTask.getQuantifier() == 0)))
				|| ((fun.equals("and")) && (eTask.getQuantifier() == 1))) {
			System.out.print("distributivity, quantifier: " + eTask.getQuantifier() + "\n");
			// split in disjuncts
			final Term[] xnfOuter = QuantifierUtils.getXjunctsOuter(eTask.getQuantifier(), eTask.getTerm());
			final Set<EliminationTask> recursion = new HashSet<EliminationTask>();
			for (final Term term : xnfOuter) {
				final EliminationTask disemt = new EliminationTask(eTask.getQuantifier(), eTask.getEliminatees(), term);
				recursion.add(elimAllRec(disemt));
			}
			// Build new Task
			final Set<TermVariable> neweleminatees = new HashSet<>();
			final Collection<Term> xjuncts = new HashSet<Term>();
			for (final EliminationTask task : recursion) {
				neweleminatees.addAll(task.getEliminatees());
				xjuncts.add(task.getTerm());
			}
			final Term newterm = QuantifierUtils.applyCorrespondingFiniteConnective(mScript, eTask.getQuantifier(),
					xjuncts);
			System.out.print("distributivity used, newterm: " + newterm + "\n");
			return new EliminationTask(eTask.getQuantifier(), neweleminatees, newterm);
		}

		return eTask;
	}

	/*
	 * Array elimination with at least 2 select terms
	 */

	public EliminationTask elimMultiSelectNaiv(final Term eTerm, final TermVariable eliminate, final int quantifier) {
		if (eTerm instanceof ApplicationTerm) {
			// Get Select Terms
			final MultiDimensionalSelect MDS = new MultiDimensionalSelect(eTerm);
			final List<MultiDimensionalSelect> Selectterms = MDS.extractSelectDeep(eTerm, false);

			// Build Select Term Combinations without repetition, with quantified array as
			// argument.
			final Set<Pair<MultiDimensionalSelect, MultiDimensionalSelect>> IndexCombinations = new HashSet<Pair<MultiDimensionalSelect, MultiDimensionalSelect>>();
			for (final MultiDimensionalSelect i : Selectterms) {
				for (final MultiDimensionalSelect j : Selectterms) {

					if ((eliminate.equals(i.getSelectTerm().getParameters()[0]))
							&& (eliminate.equals(j.getSelectTerm().getParameters()[0]))) {
						if (i != j) {
							if (!IndexCombinations
									.contains(new Pair<MultiDimensionalSelect, MultiDimensionalSelect>(j, i))) {
								IndexCombinations.add(new Pair<MultiDimensionalSelect, MultiDimensionalSelect>(i, j));
							}
						}
					}
				}
			}
			for (final MultiDimensionalSelect i : Selectterms) {

				if (eliminate.equals(i.getSelectTerm().getParameters()[0])) {
					if (IndexCombinations.size() == 0) {
						IndexCombinations.add(new Pair<MultiDimensionalSelect, MultiDimensionalSelect>(i, i));
					}
				}
			}

			// Build Up Term: Implikation
			final Set<TermVariable> neweliminatees = new HashSet<TermVariable>();
			Term newTerm = mScript.term("true");
			final Map<Term, Term> submap = new HashMap();
			System.out.print("IndexCombinations: " + IndexCombinations + "\n");
			for (final Pair<MultiDimensionalSelect, MultiDimensionalSelect> comb : IndexCombinations) {
				// new Exists Quantified variables: si_counter / sj_counter
				TermVariable si = mMgdScript.constructFreshTermVariable("si",
						comb.getFirst().getSelectTerm().getSort());
				TermVariable sj = mMgdScript.constructFreshTermVariable("sj",
						comb.getFirst().getSelectTerm().getSort());

				if (!submap.containsKey(comb.getFirst().getSelectTerm())) {
					neweliminatees.add(si);
					submap.put(comb.getFirst().getSelectTerm(), si);
				} else {
					si = (TermVariable) submap.get(comb.getFirst().getSelectTerm());
				}
				if (!submap.containsKey(comb.getSecond().getSelectTerm())) {
					neweliminatees.add(sj);
					submap.put(comb.getSecond().getSelectTerm(), sj);
				} else {
					sj = (TermVariable) submap.get(comb.getSecond().getSelectTerm());
				}

				Term iEvE = SmtUtils.indexEqualityImpliesValueEquality(mScript, comb.getFirst().getIndex(),
						comb.getSecond().getIndex(), si, sj);
				if (quantifier == QuantifiedFormula.FORALL) {
					iEvE = SmtUtils.not(mScript, iEvE);
				}

				newTerm = SmtUtils.and(mScript, iEvE, newTerm);

			}

			final Substitution sub = new Substitution(mMgdScript, submap);
			final Term newTerm2 = sub.transform(eTerm);
			if (quantifier == QuantifiedFormula.FORALL) {
				newTerm = SmtUtils.or(mScript, newTerm2, newTerm);
			} else {
				newTerm = SmtUtils.and(mScript, newTerm2, newTerm);
			}

			System.out.print("newTerm: " + newTerm.toStringDirect() + "\n");

			neweliminatees.add(eliminate); // add all not elimiatet
			// quantified variables back

			newTerm = SmtUtils.quantifier(mScript, quantifier, neweliminatees, newTerm);
			final Term nnf = new NnfTransformer(mMgdScript, mServices, QuantifierHandling.KEEP).transform(newTerm);
			final Term pushed = new QuantifierPusher(mMgdScript, mServices, true, PqeTechniques.ALL_LOCAL)
					.transform(nnf);
			final Term pnf = new PrenexNormalForm(mMgdScript).transform(pushed);
			final QuantifierSequence qs = new QuantifierSequence(mScript, pnf);
			if (qs.getNumberOfQuantifierBlocks() >= 1) {
				throw new AssertionError("quantifier sequence with alternations " + qs);
			}
			if (qs.getNumberOfQuantifierBlocks() == 1) {
				final QuantifiedVariables qv = qs.getQuantifierBlocks().iterator().next();
				if (!qv.getVariables().equals(neweliminatees)) {
					throw new AssertionError("neweliminateees and quantified variables in formula are differnt");
				}
			}
			final Term matrix = qs.getInnerTerm();
			newTerm = matrix;			
			final EliminationTask result = new EliminationTask(quantifier, neweliminatees, newTerm);
			return result;
		}
		final Set<TermVariable> oldeliminatees = new HashSet<TermVariable>();
		oldeliminatees.add(eliminate);
		final EliminationTask result = new EliminationTask(quantifier, oldeliminatees, eTerm);
		return result;
	}

	/*
	 * Eliminates one Store operation (Store a i v) with an quantified Array "a". -
	 * It replaces the Store term (Store a i v) with a new Exists quantified Array
	 * Variable a_new and adds the Conjunct "a_new = (Store a i v)".
	 *
	 * - We collect all Indices of the Input Term - We Build a new SubTerm - We
	 * eliminate the new Index Forall Quantifier with the collected Indices. - We
	 * Replace "a_new = (Store a i v)" with the new SubTerm.
	 *
	 * Returns an EliminationTask. Its Term has no more Store Operation and no new
	 * Quantifiers.
	 *
	 */

	private EliminationTask elim1StoreQuantifier(final EliminationTask eTask) {
		final MultiDimensionalStore mds = new MultiDimensionalStore(eTask.getTerm());
		final List<MultiDimensionalStore> storeterms = mds.extractArrayStoresDeep(eTask.getTerm());
		Term newterm = eTask.getTerm();
		final Set<TermVariable> neweliminatees2 = new HashSet<TermVariable>();
		// for store new exists array a1 quantifier
		for (final MultiDimensionalStore term : storeterms) {
			if (mEliminatees.contains(term.getArray())) {
				final TermVariable newarrayvar = mMgdScript.constructFreshTermVariable("a_new",
						term.getArray().getSort());
				final Set<TermVariable> neweliminatees = new HashSet<TermVariable>();
				neweliminatees.add(newarrayvar);
				// Substitute Store term with new Exist quantified Array Variable a_new
				// TODO FIX F�R MULTIDIMSTORE
				Substitution sub = new Substitution(mMgdScript,
						Collections.singletonMap(term.getStoreTerm(), newarrayvar));

				newterm = sub.transform(newterm);
				// Add conjunct a1 = (eliminated store term)
				final Term eqterm = SmtUtils.binaryEquality(mScript, newarrayvar, term.getStoreTerm());
				newterm = SmtUtils.and(mScript, newterm, eqterm);

				final TermVariable newindexvar = mMgdScript.constructFreshTermVariable("j",
						term.getStoreTerm().getParameters()[1].getSort());
				neweliminatees2.add(newindexvar);
				// Build new Term forall Indices of indexSet
				// Term 1: ((i != j) => (a_new[i] = a[i]))
				final Term indexnoteq = SmtUtils.not(mScript,
						SmtUtils.binaryEquality(mScript, newindexvar, term.getStoreTerm().getParameters()[1]));
				final Term arrayeq = SmtUtils.binaryEquality(mScript,
						SmtUtils.select(mScript, newarrayvar, newindexvar),
						SmtUtils.select(mScript, term.getArray(), newindexvar));
				final Term elimtermlhs = SmtUtils.implies(mScript, indexnoteq, arrayeq);
				// Term 2: ((i = j) => (a_new[i] = v))
				final Term indexeq = SmtUtils.binaryEquality(mScript, newindexvar,
						term.getStoreTerm().getParameters()[1]);
				final Term selectvalue = SmtUtils.binaryEquality(mScript,
						SmtUtils.select(mScript, newarrayvar, newindexvar), term.getStoreTerm().getParameters()[2]);
				final Term elimtermrhs = SmtUtils.implies(mScript, indexeq, selectvalue);
				// Term 3: Term 1 AND Term 2
				final Term elimterm = SmtUtils.and(mScript, elimtermlhs, elimtermrhs);
				// Substitute Store term equality with the new Term "elimForall"
				sub = new Substitution(mMgdScript, Collections.singletonMap(eqterm, elimterm));
				newterm = sub.transform(newterm);

//				newterm = QuantifierUtils.transformToXnf(mServices, mScript, quantifier, freshTermVariableConstructor, newterm, xnfConversionTechnique)
				
				// DER on a_new. To eliminate the new Exist Quantifier: "Exists a_new"
				final XnfDer xnfDer = new XnfDer(mMgdScript, mServices);
				final Term[] oldParams = QuantifierUtils.getXjunctsOuter(0, newterm);
				final Term[] newParams = new Term[oldParams.length];
				for (int i = 0; i < oldParams.length; i++) {
					final Set<TermVariable> eliminateesDER = new HashSet<>(neweliminatees);
					final Term[] oldAtoms = QuantifierUtils.getXjunctsInner(0, oldParams[i]);
					newParams[i] = QuantifierUtils.applyDualFiniteConnective(mScript, 0,
							Arrays.asList(xnfDer.tryToEliminate(0, oldAtoms, eliminateesDER)));
				}
				mEliminatees.addAll(neweliminatees);
				System.out.print("Store Elim Naiv: " + newterm.toStringDirect() + "\n");
				newterm = QuantifierUtils.applyCorrespondingFiniteConnective(mScript, 0, newParams);

			}
		}

		// SELECT ELIM

		EliminationTask newETask = new EliminationTask(eTask.getQuantifier(), mEliminatees, newterm);
		System.out.print("1mEliminatees: " + mEliminatees + "\n");
		for (final TermVariable qArray : mEliminatees) {
			newETask = elimMultiSelectNaiv(newETask.getTerm(), qArray, newETask.getQuantifier());
		}

		// Add Forall Quantorzz
		final Term termWForall = SmtUtils.quantifier(mScript, 1, neweliminatees2, newETask.getTerm());

		final EliminationTask result = new EliminationTask(newETask.getQuantifier(), newETask.getEliminatees(),
				termWForall);

		return result;
	}

}
