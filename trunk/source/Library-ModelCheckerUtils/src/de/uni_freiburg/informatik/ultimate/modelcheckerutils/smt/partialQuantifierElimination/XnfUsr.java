package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;

public class XnfUsr extends XjunctPartialQuantifierElimination {
	
	private final Set<TermVariable> affectedEliminatees = new HashSet<>();

	public XnfUsr(Script script, IUltimateServiceProvider services) {
		super(script, services);
	}

	@Override
	public String getName() {
		return "unimportant select removal";
	}

	@Override
	public String getAcronym() {
		return "USR";
	}

	@Override
	public Term[] tryToEliminate(int quantifier, Term[] inputAtoms,
			Set<TermVariable> eliminatees) {
		HashRelation<TermVariable, Term> var2arrays = new HashRelation<TermVariable, Term>();
		HashRelation<TermVariable, Term> var2parameters = new HashRelation<TermVariable, Term>();
		Set<TermVariable> blacklist = new HashSet<TermVariable>();
		for (Term param : inputAtoms) {
			Set<ApplicationTerm> storeTerms = (new ApplicationTermFinder("store", true)).findMatchingSubterms(param);
			if (storeTerms.isEmpty()) {
				List<MultiDimensionalSelect> slects = MultiDimensionalSelect.extractSelectDeep(param, false);
				for (MultiDimensionalSelect mds : slects) {
					Set<TermVariable> indexFreeVars = mds.getIndex().getFreeVars();
					for (TermVariable tv : indexFreeVars) {
						if (eliminatees.contains(tv)) {
							var2arrays.addPair(tv, mds.getArray());
							var2parameters.addPair(tv, param);
						}
					}
				}
			} else {
				//if there are store terms all occurring variables become
				//blacklisted
				blacklist.addAll(Arrays.asList(param.getFreeVars()));
			}
			
		}
		Set<Term> superfluousParams = new HashSet<Term>();
		for (TermVariable eliminatee : var2arrays.getDomain()) {
			if (!blacklist.contains(eliminatee)) {
				if (var2arrays.getImage(eliminatee).size() == 1 &&
						var2parameters.getImage(eliminatee).size() == 1) {
					superfluousParams.addAll(var2parameters.getImage(eliminatee));
					affectedEliminatees.add(eliminatee);
				}
			}
		}
		ArrayList<Term> resultAtoms = new ArrayList<Term>();
		for (Term oldParam : inputAtoms) {
			if (!superfluousParams.contains(oldParam)) {
				resultAtoms.add(oldParam);
			}
		}
		return resultAtoms.toArray(new Term[resultAtoms.size()]);
	}

	public Set<TermVariable> getAffectedEliminatees() {
		return affectedEliminatees;
	}
	
	

}
