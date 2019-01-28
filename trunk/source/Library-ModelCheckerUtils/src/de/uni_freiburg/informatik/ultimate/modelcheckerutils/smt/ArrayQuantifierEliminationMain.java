package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.pqe.XnfDer;
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
			System.out.print("�userste Function: " + appterm.getFunction().getName() + "\n");
			// TODO Dualit�ts Umformung
			if (eTask.getQuantifier() == QuantifiedFormula.EXISTS) {
				System.out.print("Quantifier Type is Exists" + "\n");
				if ((appterm.getFunction().getName().equals("and"))) {
					// TODO Count Store/Select Axioms
					Term taskTerm = result.getTerm();
					taskTerm = selectOverStore(taskTerm);
					result = new EliminationTask(result.getQuantifier(), result.getEliminatees(), taskTerm);
					result = elim1Store(result);
					result = distributivity(result, appterm.getFunction().getName());
					result = termInconsistents(result);
					result = elimMultiSelectNaiv(result); // TODO Achtung, entfernt einfach
				} else if ((appterm.getFunction().getName().equals("or"))) {

					result = distributivity(result, appterm.getFunction().getName());
				}

			} else if (eTask.getQuantifier() == QuantifiedFormula.FORALL) { // TODO Or CHECK DUALITY
																			// appterm.getFunction().getName().equals("or")
				System.out.print("Quantifier Type is Forall" + "\n");
				throw new UnsupportedOperationException("Quantifier Type is Forall" + "\n");
			}
		}
		return result;

	}

	/*
	 * TODO Store over Store rekursiv. Nur eliminieren, wenn Indexe Gleich.
	 * ThreeValueEq nutzen
	 */
	private Term storeOverStore(final Term term) {
		return term;
	}

	/*
	 * Rekursion Gets all Select Terms. If the Array is not inestance of
	 * VariableTerm, its a Store Term. Then we Replace term with newterm, using the
	 * following Rule:
	 *
	 * TODO Optimierung Index gleichheit
	 *
	 */
	private Term selectOverStore(final Term term) {
		final MultiDimensionalSelect mds = new MultiDimensionalSelect(term);
		final List<MultiDimensionalSelect> Selectterms = mds.extractSelectDeep(term, false);
		for (final MultiDimensionalSelect select : Selectterms) {
			// extract to method

			// if Array is TermVariable, its no SelectOverStore
			if (!(select.getArray() instanceof TermVariable)) {
				final MultiDimensionalStore mds2 = new MultiDimensionalStore(select.getArray());

				// useless
				final List<MultiDimensionalStore> innerStore = mds2.extractArrayStoresShallow(select.getArray());
				// use Collections.singletonMap(key, value)
				final Map<Term, Term> submap = new HashMap();
				// 2 Substitutions for IndexEQ and IndexNEQ
				submap.put(select.getSelectTerm(), innerStore.get(0).getValue());
				final Substitution sub = new Substitution(mMgdScript, submap);
				final Term subtermlhs = sub.transform(term);
				submap.clear();
				submap.put(select.getSelectTerm(),
						SmtUtils.select(mScript, innerStore.get(0).getArray(), select.getIndex().get(0)));
				final Substitution sub2 = new Substitution(mMgdScript, submap);
				final Term subtermrhs = sub2.transform(term);
				submap.clear();
				// Index comparison
				final Term indexeq = SmtUtils.binaryEquality(mScript, innerStore.get(0).getIndex().get(0),
						select.getIndex().get(0));
				final Term indexnoteq = SmtUtils.not(mScript, SmtUtils.binaryEquality(mScript,
						innerStore.get(0).getIndex().get(0), select.getIndex().get(0)));
				final Term lhs = SmtUtils.and(mScript, indexeq, subtermlhs);
				final Term rhs = SmtUtils.and(mScript, indexnoteq, subtermrhs);
				final Term newterm = SmtUtils.or(mScript, lhs, rhs);

				return selectOverStore(newterm);
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
	 * TODO more than one eliminatee
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
			final TermVariable newarrayvar = mScript.variable("a_new_" + counter, term.getArray().getSort());
			final Set<TermVariable> neweliminatees = new HashSet<TermVariable>();
			neweliminatees.add(newarrayvar);
			// Substitute Store term with new Exist quantified Array Variable a_new
			final Map<Term, Term> submap = new HashMap();
			submap.put(term.getStoreTerm(), newarrayvar);
			Substitution sub = new Substitution(mMgdScript, submap);
			submap.clear();
			newterm = sub.transform(eTask.getTerm());
			// Add conjunct a1 = (eliminated store term)
			final Term eqterm = SmtUtils.binaryEquality(mScript, newarrayvar, term.getStoreTerm());
			newterm = SmtUtils.and(mScript, newterm, eqterm);
			final TermVariable newindexvar = mScript.variable("j_" + counter, SmtSortUtils.getIntSort(mMgdScript));
			neweliminatees2.add(newindexvar);
			// Build new Term forall Indices of indexSet
			Term elimForall = mScript.term("true"); // neutral Element for Conjunction
			final Set<Term> indexSet = collectArrayIndices(eTask.getTerm());
			indexSet.remove(newindexvar);
			for (final Term indexvar : indexSet) {
				// Term 1: ((i != j) => (a_new[i] = a[i]))
				final Term indexnoteq = SmtUtils.not(mScript,
						SmtUtils.binaryEquality(mScript, indexvar, term.getStoreTerm().getParameters()[1]));
				final Term arrayeq = SmtUtils.binaryEquality(mScript, SmtUtils.select(mScript, newarrayvar, indexvar),
						SmtUtils.select(mScript, term.getArray(), indexvar));
				final Term elimtermlhs = SmtUtils.implies(mScript, indexnoteq, arrayeq);
				// Term 2: ((i = j) => (a_new[i] = v))
				final Term indexeq = SmtUtils.binaryEquality(mScript, indexvar, term.getStoreTerm().getParameters()[1]);
				final Term selectvalue = SmtUtils.binaryEquality(mScript, SmtUtils.select(mScript, newarrayvar, indexvar),
						term.getValue());
				final Term elimtermrhs = SmtUtils.implies(mScript, indexeq, selectvalue);
				// Term 3: Term 1 AND Term 2
				final Term elimterm = SmtUtils.and(mScript, elimtermlhs, elimtermrhs);
				// elimForall AND Term 3
				elimForall = SmtUtils.and(mScript, elimForall, elimterm);
			}
			// Substitute Store term equality with the new Term "elimForall"
			submap.put(eqterm, elimForall);
			sub = new Substitution(mMgdScript, submap);
			newterm = sub.transform(newterm);
			submap.clear();
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

		final EliminationTask noStoreTerm = new EliminationTask(eTask.getQuantifier(), eTask.getEliminatees(), newterm);
		return noStoreTerm;
	}

	private EliminationTask arrayEQ(final EliminationTask eTask) {
		final EliminationTask result = eTask;

		return result;
	}

	/*
	 * Stores all Equalitys of an conjunction and Checks for Inconsistens. It's
	 * basically not a quantifier elimination, but it can eliminate one. It's cheap
	 * and can shorten the Term.
	 *
	 * TODO: If Functions is OR, check for Tautologi Use Equality/Disequality
	 * Informations Global
	 */

	private EliminationTask termInconsistents(final EliminationTask eTask) {
		final EliminationTask result = eTask;
		final ThreeValuedEquivalenceRelation<Term> tver = new ThreeValuedEquivalenceRelation<Term>();
		final ApplicationTerm appterm = (ApplicationTerm) eTask.getTerm(); // wird in elimAllRec �berpr�ft

		if (SmtUtils.isFunctionApplication(eTask.getTerm(), "and") && (eTask.getQuantifier() == 0)) {
			for (final Term term : appterm.getParameters()) {
				if (term.getSort().getName().equals("Bool")) {
					final ApplicationTerm boolterm = (ApplicationTerm) term;
					if (boolterm.getFunction().getName().equals("=")) {
						// Add Equality
						tver.addElement(boolterm.getParameters()[0]);
						tver.addElement(boolterm.getParameters()[1]);
						tver.reportEquality(boolterm.getParameters()[0], boolterm.getParameters()[1]);

					} else if (boolterm.getFunction().getName().equals("not")) {
						// Add Disequality
						final ApplicationTerm eqterm = (ApplicationTerm) boolterm.getParameters()[0];
						tver.addElement(eqterm.getParameters()[0]);
						tver.addElement(eqterm.getParameters()[1]);
						tver.reportDisequality(eqterm.getParameters()[0], eqterm.getParameters()[1]);

					}
				}
				if ((tver.isInconsistent()) && (!tver.getAllElements().isEmpty())) {
					return new EliminationTask(eTask.getQuantifier(), eTask.getEliminatees(), mScript.term("false"));
				}
				// if ((tver.isTautological()) && (!tver.getAllElements().isEmpty())) { //Nur
				// f�r OR
				// System.out.print("return\n");
				// return new EliminationTask(eTask.getQuantifier(), eTask.getEliminatees(),
				// mScript.term("true"));
				// }

			}
		}

		return result;
	}

	/*
	 * Distributivit�t TODO Code Duplication removen eTask hast the Term, we want to
	 * use distributivity on fun ist "and" or "or"
	 */

	private EliminationTask distributivity(final EliminationTask eTask, final String fun) {
		System.out.print("distributivity used " + "\n");
		if ((fun.equals("or") && (eTask.getQuantifier() == 0))) {
			// split in disjuncts
			final Term[] disjuncts = SmtUtils.getDisjuncts(eTask.getTerm());
			final Set<EliminationTask> recursion = new HashSet<EliminationTask>();
			for (final Term term : disjuncts) {
				final EliminationTask disjunctemt = new EliminationTask(eTask.getQuantifier(), eTask.getEliminatees(), term);
				recursion.add(elimAllRec(disjunctemt));
			}
			// Build new Task
			final Set<TermVariable> neweleminatees = new HashSet<>();
			Term newterm = recursion.iterator().next().getTerm();
			for (final EliminationTask task : recursion) {
				task.getQuantifier();
				neweleminatees.addAll(task.getEliminatees());
				newterm = SmtUtils.or(mScript, newterm, task.getTerm());

			}
			System.out.print("distributivity used, newterm: " + newterm + "\n");
			return new EliminationTask(eTask.getQuantifier(), neweleminatees, newterm);
		} else if ((fun.equals("and")) && (eTask.getQuantifier() == 1)) {
			// split in conjunkts
			final Term[] conjuncts = SmtUtils.getConjuncts(eTask.getTerm());
			final Set<EliminationTask> recursion = new HashSet<EliminationTask>();
			for (final Term term : conjuncts) {
				final EliminationTask conjunctemt = new EliminationTask(eTask.getQuantifier(), eTask.getEliminatees(), term);
				recursion.add(elimAllRec(conjunctemt));
			}
			// Build new Task
			final Set<TermVariable> neweleminatees = new HashSet<>();
			Term newterm = recursion.iterator().next().getTerm();
			for (final EliminationTask task : recursion) {
				task.getQuantifier();
				neweleminatees.addAll(task.getEliminatees());
				newterm = SmtUtils.and(mScript, newterm, task.getTerm());

			}
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
	 * terms like Finnland example
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

			System.out.print("Combinations: " + IndexCombinations + "\n");

			// Build Up Term: Implikation
			int counter = 0;
			final Set<TermVariable> neweliminatees = new HashSet<TermVariable>();
			Term newTerm = eTask.getTerm();
			final Map<Term, Term> submap = new HashMap();
			for (final Pair<MultiDimensionalSelect, MultiDimensionalSelect> comb : IndexCombinations) {
				// new Exists Quantified variables: si_counter / sj_counter
				final TermVariable si = mScript.variable("si_" + counter, SmtSortUtils.getIntSort(mMgdScript));
				final TermVariable sj = mScript.variable("sj_" + counter, SmtSortUtils.getIntSort(mMgdScript));
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
			if (!neweliminatees.isEmpty()) {
				newTerm = newTerm;
			}
			return new EliminationTask(eTask.getQuantifier(), neweliminatees, newTerm);
		}
		return null;
	}
}