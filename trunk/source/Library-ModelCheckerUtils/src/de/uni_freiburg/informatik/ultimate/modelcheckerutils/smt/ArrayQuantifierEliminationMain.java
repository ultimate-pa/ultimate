package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
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

	public ArrayQuantifierEliminationMain(final ManagedScript mgdScript, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique) {
		super();
		mMgdScript = mgdScript;
		mScript = mMgdScript.getScript();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
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
	public EliminationTask elimAllRec(final EliminationTask eTask) {
		System.out.print("New Array Elimination USED\n");
		EliminationTask result = eTask;
		System.out.print("Zu eliminieren: " + eTask.getEliminatees() + "\n");
		System.out.print("Term: " + eTask.getTerm() + "\n");
		if (eTask.getTerm() instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) eTask.getTerm();

			// TODO Count Store/Select Axioms

			ThreeValuedEquivalenceRelation tVER = calcThreeValuedEquiRel(result); //TODO use in all Index comparisons
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
//			taskTerm = storeOverStore(taskTerm, eTask.getEliminatees(), tVER); //TODO REWORK 
//			taskTerm = selectOverStore(taskTerm, eTask.getEliminatees(), tVER);		 //TODO REWORK 	
			result = new EliminationTask(result.getQuantifier(), eTask.getEliminatees(), taskTerm);
			
			result = elim1Store(result);
			result = distributivity(result, appterm.getFunction().getName());
			result = elimMultiSelectNaiv(result);

		}
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

	private Term eliminateEQ(final Term term, Set<TermVariable> eliminatees) {
		Term noeqterm = term;
		collectArrayIndices(term);
		// find Array EQ DEQ in term.
		ApplicationTermFinder atfeq = new ApplicationTermFinder("=", false);
		Set<ApplicationTerm> eqSet = atfeq.findMatchingSubterms(term);
		for (ApplicationTerm appterm : eqSet) {
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
								if(indexvar1 == indexvar2) {
									// Build newterm for EQ.
									Term select1 = SmtUtils.select(mScript, appterm.getParameters()[0], indexvar1);
									Term select2 = SmtUtils.select(mScript, appterm.getParameters()[1], indexvar2);
									Term newEquailtyPart = SmtUtils.binaryEquality(mScript, select1, select2);
									newEquailty = SmtUtils.and(mScript, newEquailtyPart, newEquailty);
								}

							}
						}
						// Substitude newterms
						final Map<Term, Term> submap = new HashMap();
						submap.put(appterm, newEquailty);
						Substitution sub = new Substitution(mMgdScript, submap);
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
	private Term storeOverStore(final Term term, Set<TermVariable> eliminatees, ThreeValuedEquivalenceRelation tVER) {
		final MultiDimensionalStore mds = new MultiDimensionalStore(term);
		final List<MultiDimensionalStore> Storeterms = mds.extractArrayStoresShallow(term);
		for (final MultiDimensionalStore storeOuter : Storeterms) {
			// if Array is BasicArray, its no SelectOverStore
			if (!SmtUtils.isBasicArrayTerm(storeOuter.getArray())) {
				final MultiDimensionalStore storeInner = new MultiDimensionalStore(storeOuter.getArray());
				if ((SmtUtils.isBasicArrayTerm(storeInner.getArray()))) {
					// End of Store over store queue recursion
					if (eliminatees.contains(storeInner.getArray())) {
						/* if() { // Indexe Gleich:
						 * 
						 * } else { return term;// was else ka }
						 */						
						if(tVER.getEqualityStatus(storeInner.getIndex().get(0), storeOuter.getIndex().get(0)).compareTo(EqualityStatus.EQUAL) == 0) {
							
						}	
					}
				} else if (storeInner != null) { // GO in recursion
					return storeOverStore(term, eliminatees, tVER);
				}
			}
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
	private Term selectOverStore(final Term term, Set<TermVariable> eliminatees, ThreeValuedEquivalenceRelation tVER) {
		final MultiDimensionalSelect mds = new MultiDimensionalSelect(term);
		final List<MultiDimensionalSelect> Selectterms = mds.extractSelectDeep(term, false);
		for (final MultiDimensionalSelect select : Selectterms) {
			// extract to method

			// if Array is BasicArray, its no SelectOverStore
			if (!SmtUtils.isBasicArrayTerm(select.getArray())) {
				final MultiDimensionalStore innerStore = new MultiDimensionalStore(select.getArray());
				if ((SmtUtils.isBasicArrayTerm(innerStore.getArray()))) {
					if (eliminatees.contains(innerStore.getArray())) {
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
						if (tVER.getDisequalities().containsPair(innerStore.getIndex().get(0), select.getIndex().get(0))) {
							indexeq = mScript.term("false");
						} else if(tVER.getEqualityStatus(innerStore.getIndex().get(0), select.getIndex().get(0)).compareTo(EqualityStatus.EQUAL) == 0) {
							indexeq = mScript.term("true");
						}		
						// Index comparison DisEquality					
						Term indexnoteq = SmtUtils.not(mScript, SmtUtils.binaryEquality(mScript,
								innerStore.getIndex().get(0), select.getIndex().get(0)));						
						if (tVER.getDisequalities().containsPair(innerStore.getIndex().get(0), select.getIndex().get(0))) {
							indexnoteq = mScript.term("true");
						} else if(tVER.getEqualityStatus(innerStore.getIndex().get(0), select.getIndex().get(0)).compareTo(EqualityStatus.EQUAL) == 0) {
							indexnoteq = mScript.term("false");
						}
						
						final Term lhs = SmtUtils.and(mScript, indexeq, subtermlhs);
						final Term rhs = SmtUtils.and(mScript, indexnoteq, subtermrhs);
						final Term newterm = SmtUtils.or(mScript, lhs, rhs);

						return selectOverStore(newterm, eliminatees, tVER);
					}
				} else if (innerStore != null) { // TODO Select over Store Over Store....
					return storeOverStore(term, eliminatees, tVER);
				}
			}
		}

		return term;
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
	private EliminationTask elim1Store(final EliminationTask eTask) {
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
			Collection<Term> xjuncts = new HashSet<Term>();
			for (final EliminationTask task : recursion) {
				neweleminatees.addAll(task.getEliminatees());
				xjuncts.add(task.getTerm());
			}
			Term newterm = QuantifierUtils.applyCorrespondingFiniteConnective(mScript, eTask.getQuantifier(), xjuncts);
			System.out.print("distributivity used, newterm: " + newterm + "\n");
			return new EliminationTask(eTask.getQuantifier(), neweleminatees, newterm);
		}

		return eTask;
	}

	/*
	 * Gets the Appterm in form (and (= v (select a i))(= v (select a i).....) array
	 * is a returns all select index value Pairs with a as second argument of the
	 * select term
	 *
	 * TODO There is no use atm.
	 *
	 */
	private Set<Pair<Term, Term>> calcArInVaSet(final ApplicationTerm appterm, final TermVariable array) {
		final Set<Pair<Term, Term>> ArInVaPairs = new HashSet<Pair<Term, Term>>();
		for (int i = 0; i < appterm.getParameters().length; i++) {
			final ApplicationTerm SubAppTerm = (ApplicationTerm) appterm.getParameters()[i];
			final ApplicationTerm SubATerm = (ApplicationTerm) SubAppTerm.getParameters()[0];
			if (SubATerm.getFunction().getName().equals("select")) { // Selectterm?
				// Quantifier im select term?
				if (array == SubATerm.getParameters()[0]) {
					// Selectterm.getParameters()[1],subappterm.getParameters()[1] //Index,Value
					// Array Index value; liste aufbaun
					ArInVaPairs.add(new Pair<Term, Term>(SubATerm.getParameters()[1], SubAppTerm.getParameters()[1]));

				}

			}

		}

		return ArInVaPairs;
	}

	/*
	 * Simple Select elimination, working only if there are nothing else than select
	 * terms like Finnland test
	 * 
	 * TODO check if Sweden test is correct
	 */

	public EliminationTask elimMultiSelectNaiv(final EliminationTask eTask) {
		System.out.print("Using elimMultiSelectNaiv to Eliminate\n");
		if (eTask.getTerm() instanceof ApplicationTerm) {
			// Get Select Terms
			final MultiDimensionalSelect MDS = new MultiDimensionalSelect(eTask.getTerm());

			final List<MultiDimensionalSelect> Selectterms = MDS.extractSelectDeep(eTask.getTerm(), false);
			for (final MultiDimensionalSelect selectTerm : MDS.extractSelectDeep(eTask.getTerm(), false)) {
				if (selectTerm.getArray().equals(eTask.getEliminatees())) { // Check if Quantifier in Select
																			// Term
					// Construct Index newVar Pairs
					MDS.extractSelectDeep(eTask.getTerm(), false).get(0).getIndex(); // Index
				}
			}

			// Build Select Term Combinations without repetition, with quantified array as
			// argument.
			final Set<Pair<MultiDimensionalSelect, MultiDimensionalSelect>> IndexCombinations = new HashSet<Pair<MultiDimensionalSelect, MultiDimensionalSelect>>();
			for (final MultiDimensionalSelect i : Selectterms) {
				for (final MultiDimensionalSelect j : Selectterms) {

					if ((eTask.getEliminatees().contains(i.getSelectTerm().getParameters()[0]))
							&& (eTask.getEliminatees().contains(j.getSelectTerm().getParameters()[0]))) {
						if (i != j) {
							if (!IndexCombinations
									.contains(new Pair<MultiDimensionalSelect, MultiDimensionalSelect>(j, i))) {
								IndexCombinations.add(new Pair<MultiDimensionalSelect, MultiDimensionalSelect>(i, j));
							}
						}
					}
				}
			}
			// Build Up Term: Implikation
			int counter = 0;
			final Set<TermVariable> neweliminatees = new HashSet<TermVariable>();
			Term newTerm = eTask.getTerm();
			final Map<Term, Term> submap = new HashMap();
			for (final Pair<MultiDimensionalSelect, MultiDimensionalSelect> comb : IndexCombinations) {
				// new Exists Quantified variables: si_counter / sj_counter
				final TermVariable si = mScript.variable("si_" + counter, comb.getFirst().getSelectTerm().getSort());
				final TermVariable sj = mScript.variable("sj_" + counter, comb.getSecond().getSelectTerm().getSort());
				counter += 1;
				neweliminatees.add(si);
				neweliminatees.add(sj);
				submap.put(comb.getFirst().getSelectTerm(), si);
				submap.put(comb.getSecond().getSelectTerm(), sj);

				final Term iEvE = SmtUtils.indexEqualityImpliesValueEquality(mScript, comb.getFirst().getIndex(),
						comb.getSecond().getIndex(), si, sj);
				newTerm = SmtUtils.and(mScript, iEvE, newTerm);
			}
			final Substitution sub = new Substitution(mMgdScript, submap);
			newTerm = sub.transform(newTerm);
			newTerm = SmtUtils.quantifier(mScript, eTask.getQuantifier(), neweliminatees, newTerm);
			System.out.print("newTerm: " + newTerm.toStringDirect() + "\n");
			neweliminatees.addAll(eTask.getEliminatees()); // add all not elimiatet quantified variables back
			return new EliminationTask(eTask.getQuantifier(), neweliminatees, newTerm);
		}
		return null;
	}
}