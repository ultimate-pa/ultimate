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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.pqe.XnfDer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;

public class ArrayQuantifierEliminationMain {

	private final ManagedScript mMgdScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private int mRecursiveCallCounter = -1;
	private Script mScript;

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
			ApplicationTerm appterm = (ApplicationTerm) eTask.getTerm();
			System.out.print("Äuserste Function: " + appterm.getFunction().getName() + "\n");
			// TODO Dualitäts Umformung
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
			}
		}
		return result;

	}

	/*
	 * TODO Store over Store rekursiv. Nur eliminieren, wenn Indexe Gleich.
	 * ThreeValueEq nutzen
	 */
	private Term storeOverStore(Term term) {
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
	private Term selectOverStore(Term term) {
		MultiDimensionalSelect mds = new MultiDimensionalSelect(term);
		List<MultiDimensionalSelect> Selectterms = mds.extractSelectDeep(term, false);
		for (MultiDimensionalSelect select : Selectterms) {
			// if Array is TermVariable, its no SelectOverStore
			if (!(select.getArray() instanceof TermVariable)) {
				MultiDimensionalStore mds2 = new MultiDimensionalStore(select.getArray());
				List<MultiDimensionalStore> innerStore = mds2.extractArrayStoresShallow(select.getArray());
				Map<Term, Term> submap = new HashMap();
				// 2 Substitutions for IndexEQ and IndexNEQ
				submap.put(select.getSelectTerm(), innerStore.get(0).getValue());
				Substitution sub = new Substitution(mMgdScript, submap);
				Term subtermlhs = sub.transform(term);
				submap.clear();
				submap.put(select.getSelectTerm(),
						SmtUtils.select(mScript, innerStore.get(0).getArray(), select.getIndex().get(0)));
				Substitution sub2 = new Substitution(mMgdScript, submap);
				Term subtermrhs = sub2.transform(term);
				submap.clear();
				// Index comparison
				Term indexeq = SmtUtils.binaryEquality(mScript, innerStore.get(0).getIndex().get(0),
						select.getIndex().get(0));
				Term indexnoteq = SmtUtils.not(mScript, SmtUtils.binaryEquality(mScript,
						innerStore.get(0).getIndex().get(0), select.getIndex().get(0)));
				Term lhs = SmtUtils.and(mScript, indexeq, subtermlhs);
				Term rhs = SmtUtils.and(mScript, indexnoteq, subtermrhs);
				Term newterm = SmtUtils.or(mScript, lhs, rhs);

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

	private Set<Term> collectArrayIndices(Term term) {

		MultiDimensionalSelect mdSelect = new MultiDimensionalSelect(term);
		List<MultiDimensionalSelect> mdSelectDeep = mdSelect.extractSelectDeep(term, false);
		MultiDimensionalStore mdStore = new MultiDimensionalStore(term);
		List<MultiDimensionalStore> mdStoreDeep = mdStore.extractArrayStoresDeep(term);
		Set<Term> indexSet = new HashSet<Term>();
		for (MultiDimensionalSelect mds : mdSelectDeep) {
			indexSet.add(mds.getIndex().get(0));
		}
		for (MultiDimensionalStore mds : mdStoreDeep) {
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
	private EliminationTask elim1Store(EliminationTask eTask) {
		MultiDimensionalStore mds = new MultiDimensionalStore(eTask.getTerm());
		List<MultiDimensionalStore> storeterms = mds.extractArrayStoresDeep(eTask.getTerm());
		int counter = 0;
		Term newterm = eTask.getTerm();
		Set<TermVariable> neweliminatees2 = new HashSet<TermVariable>();
		// for store new exists array a1 quantifier
		for (MultiDimensionalStore term : storeterms) {
			TermVariable newarrayvar = mScript.variable("a_new_" + counter, term.getArray().getSort());
			Set<TermVariable> neweliminatees = new HashSet<TermVariable>();
			neweliminatees.add(newarrayvar);
			// Substitute Store term with new Exist quantified Array Variable a_new
			Map<Term, Term> submap = new HashMap();
			submap.put(term.getStoreTerm(), newarrayvar);
			Substitution sub = new Substitution(mMgdScript, submap);
			submap.clear();
			newterm = sub.transform(eTask.getTerm());
			// Add conjunct a1 = (eliminated store term)
			Term eqterm = SmtUtils.binaryEquality(mScript, newarrayvar, term.getStoreTerm());
			newterm = SmtUtils.and(mScript, newterm, eqterm);
			TermVariable newindexvar = mScript.variable("j_" + counter, SmtSortUtils.getIntSort(mMgdScript));
			neweliminatees2.add(newindexvar);
			// Build new Term forall Indices of indexSet
			Term elimForall = mScript.term("true"); // neutral Element for Conjunction
			Set<Term> indexSet = collectArrayIndices(eTask.getTerm());
			indexSet.remove(newindexvar);
			for (Term indexvar : indexSet) {
				// Term 1: ((i != j) => (a_new[i] = a[i]))
				Term indexnoteq = SmtUtils.not(mScript,
						SmtUtils.binaryEquality(mScript, indexvar, term.getStoreTerm().getParameters()[1]));
				Term arrayeq = SmtUtils.binaryEquality(mScript, SmtUtils.select(mScript, newarrayvar, indexvar),
						SmtUtils.select(mScript, term.getArray(), indexvar));
				Term elimtermlhs = SmtUtils.implies(mScript, indexnoteq, arrayeq);
				// Term 2: ((i = j) => (a_new[i] = v))
				Term indexeq = SmtUtils.binaryEquality(mScript, indexvar, term.getStoreTerm().getParameters()[1]);
				Term selectvalue = SmtUtils.binaryEquality(mScript, SmtUtils.select(mScript, newarrayvar, indexvar),
						term.getValue());
				Term elimtermrhs = SmtUtils.implies(mScript, indexeq, selectvalue);
				// Term 3: Term 1 AND Term 2
				Term elimterm = SmtUtils.and(mScript, elimtermlhs, elimtermrhs);
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

		EliminationTask noStoreTerm = new EliminationTask(eTask.getQuantifier(), eTask.getEliminatees(), newterm);
		return noStoreTerm;
	}

	private EliminationTask arrayEQ(EliminationTask eTask) {
		EliminationTask result = eTask;

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

	private EliminationTask termInconsistents(EliminationTask eTask) {
		EliminationTask result = eTask;
		ThreeValuedEquivalenceRelation<Term> tver = new ThreeValuedEquivalenceRelation<Term>();
		ApplicationTerm appterm = (ApplicationTerm) eTask.getTerm(); // wird in elimAllRec überprüft

		if (SmtUtils.isFunctionApplication(eTask.getTerm(), "and") && (eTask.getQuantifier() == 0)) {
			for (Term term : appterm.getParameters()) {
				if (term.getSort().getName().equals("Bool")) {
					ApplicationTerm boolterm = (ApplicationTerm) term;
					if (boolterm.getFunction().getName().equals("=")) {
						// Add Equality
						tver.addElement(boolterm.getParameters()[0]);
						tver.addElement(boolterm.getParameters()[1]);
						tver.reportEquality(boolterm.getParameters()[0], boolterm.getParameters()[1]);

					} else if (boolterm.getFunction().getName().equals("not")) {
						// Add Disequality
						ApplicationTerm eqterm = (ApplicationTerm) boolterm.getParameters()[0];
						tver.addElement(eqterm.getParameters()[0]);
						tver.addElement(eqterm.getParameters()[1]);
						tver.reportDisequality(eqterm.getParameters()[0], eqterm.getParameters()[1]);

					}
				}
				if ((tver.isInconsistent()) && (!tver.getAllElements().isEmpty())) {
					return new EliminationTask(eTask.getQuantifier(), eTask.getEliminatees(), mScript.term("false"));
				}
				// if ((tver.isTautological()) && (!tver.getAllElements().isEmpty())) { //Nur
				// für OR
				// System.out.print("return\n");
				// return new EliminationTask(eTask.getQuantifier(), eTask.getEliminatees(),
				// mScript.term("true"));
				// }

			}
		}

		return result;
	}

	/*
	 * Distributivität TODO Code Duplication removen eTask hast the Term, we want to
	 * use distributivity on fun ist "and" or "or"
	 */

	private EliminationTask distributivity(EliminationTask eTask, String fun) {
		System.out.print("distributivity used " + "\n");
		if ((fun.equals("or") && (eTask.getQuantifier() == 0))) {
			// split in disjuncts
			Term[] disjuncts = SmtUtils.getDisjuncts(eTask.getTerm());
			Set<EliminationTask> recursion = new HashSet<EliminationTask>();
			for (Term term : disjuncts) {
				EliminationTask disjunctemt = new EliminationTask(eTask.getQuantifier(), eTask.getEliminatees(), term);
				recursion.add(elimAllRec(disjunctemt));
			}
			// Build new Task
			Set<TermVariable> neweleminatees = new HashSet<>();
			Term newterm = recursion.iterator().next().getTerm();
			for (EliminationTask task : recursion) {
				task.getQuantifier();
				neweleminatees.addAll(task.getEliminatees());
				newterm = SmtUtils.or(mScript, newterm, task.getTerm());

			}
			System.out.print("distributivity used, newterm: " + newterm + "\n");
			return new EliminationTask(eTask.getQuantifier(), neweleminatees, newterm);
		} else if ((fun.equals("and")) && (eTask.getQuantifier() == 1)) {
			// split in conjunkts
			Term[] conjuncts = SmtUtils.getConjuncts(eTask.getTerm());
			Set<EliminationTask> recursion = new HashSet<EliminationTask>();
			for (Term term : conjuncts) {
				EliminationTask conjunctemt = new EliminationTask(eTask.getQuantifier(), eTask.getEliminatees(), term);
				recursion.add(elimAllRec(conjunctemt));
			}
			// Build new Task
			Set<TermVariable> neweleminatees = new HashSet<>();
			Term newterm = recursion.iterator().next().getTerm();
			for (EliminationTask task : recursion) {
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
	private Set<Pair<Term, Term>> calcArInVaSet(ApplicationTerm appterm, TermVariable array) {
		Set<Pair<Term, Term>> ArInVaPairs = new HashSet<Pair<Term, Term>>();
		for (int i = 0; i < appterm.getParameters().length; i++) {
			ApplicationTerm SubAppTerm = (ApplicationTerm) appterm.getParameters()[i];
			ApplicationTerm SubATerm = (ApplicationTerm) SubAppTerm.getParameters()[0];
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
			MultiDimensionalSelect MDS = new MultiDimensionalSelect(eTask.getTerm());

			List<MultiDimensionalSelect> Selectterms = MDS.extractSelectDeep(eTask.getTerm(), false);
			for (MultiDimensionalSelect selectTerm : MDS.extractSelectDeep(eTask.getTerm(), false)) {
				if (selectTerm.getArray().equals(eTask.getEliminatees())) { // Check if Quantifier in Select
																			// Term
					// Construct Index newVar Pairs
					MDS.extractSelectDeep(eTask.getTerm(), false).get(0).getIndex(); // Index
				}
			}

			// Build Select Term Combinations without repetition, with quantified array as
			// argument.
			Set<Pair<MultiDimensionalSelect, MultiDimensionalSelect>> IndexCombinations = new HashSet<Pair<MultiDimensionalSelect, MultiDimensionalSelect>>();
			for (MultiDimensionalSelect i : Selectterms) {
				for (MultiDimensionalSelect j : Selectterms) {

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
			Set<TermVariable> neweliminatees = new HashSet<TermVariable>();
			Term newTerm = eTask.getTerm();
			Map<Term, Term> submap = new HashMap();
			for (Pair<MultiDimensionalSelect, MultiDimensionalSelect> comb : IndexCombinations) {
				// new Exists Quantified variables: si_counter / sj_counter
				TermVariable si = mScript.variable("si_" + counter, SmtSortUtils.getIntSort(mMgdScript));
				TermVariable sj = mScript.variable("sj_" + counter, SmtSortUtils.getIntSort(mMgdScript));
				counter += 1;
				neweliminatees.add(si);
				neweliminatees.add(sj);
				submap.put((Term) comb.getFirst().getSelectTerm(), (Term) si);
				submap.put((Term) comb.getSecond().getSelectTerm(), (Term) sj);

				Term iEvE = SmtUtils.indexEqualityImpliesValueEquality(mScript, comb.getFirst().getIndex(),
						comb.getSecond().getIndex(), si, sj);
				newTerm = SmtUtils.and(mScript, iEvE, newTerm);
			}
			Substitution sub = new Substitution(mMgdScript, submap);
			newTerm = sub.transform(newTerm);
			newTerm = SmtUtils.quantifier(mScript, eTask.getQuantifier(), neweliminatees, newTerm);
			System.out.print("newTerm: " + newTerm.toStringDirect() + "\n");

			neweliminatees.addAll(eTask.getEliminatees()); // add all not elimiatet quantified variables back
			if (!neweliminatees.isEmpty()) {
				newTerm = (QuantifiedFormula) newTerm;
			}
			return new EliminationTask(eTask.getQuantifier(), neweliminatees, newTerm);
		}
		return null;
	}
}
