package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

/**
 * Common abstract superclass of Cnf and Dnf.
 * In order to understand the meaning of variables names 
 * replace "outer" by "conjunct" and "inner" by "disjunct" for CNF, and
 * replace "outer" by "disjunct" and "inner" by "conjunct" for CNF.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public abstract class Xnf extends Nnf {

	public Xnf(Script script, IUltimateServiceProvider services) {
		super(script, services);
	}
	
	protected abstract class XnfTransformerHelper extends NnfTransformerHelper {

		protected XnfTransformerHelper(IUltimateServiceProvider services) {
			super(services);
		}
		public abstract String innerConnectiveSymbol();
		public abstract String outerConnectiveSymbol();
		
		public abstract String innerConnectiveNeutralElement();
		
		public abstract Term innerConnective(Script script, Term... params);
		public abstract Term outerConnective(Script script, Term... params);
		
		@Override
		public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
			String functionSymbolName = appTerm.getFunction().getName();
			Term result;
			if (functionSymbolName.equals(innerConnectiveSymbol())) {
				// case where the connective of the formula is inner connective
				// of the normal form.
				
				// result set of sets e.g. for CNF this is a conjunction of 
				// disjuncts
				HashSet<Set<Term>> resOuterSet = new HashSet<Set<Term>>();
				// for CNF we start with the empty disjunction (which is false)
				resOuterSet.add(new HashSet<Term>());
				for (Term inputInner : newArgs) {
					//e.g. for CNF we iterate over each disjunct of the input
					if ((inputInner instanceof ApplicationTerm) && 
							((ApplicationTerm) inputInner).getFunction().getName().equals(outerConnectiveSymbol())) {
						HashSet<Set<Term>> oldResOuterSet = resOuterSet;
						resOuterSet = new HashSet<Set<Term>>();
						// for CNF: if this input conjunct is a disjunction we
						// have a construct a copy of each result disjunction
						// and add this disjunct
						Term[] inputOuters = ((ApplicationTerm) inputInner).getParameters();
						product(resOuterSet, oldResOuterSet, 
								new HashSet<Term>(Arrays.asList(inputOuters)));
					} else {
						// for CNF if this input conjunct is an atom have to add
						// this atom to each result disjunction
						product(resOuterSet, inputInner);
					}
				}
				// remove all sets for which a strict subset is contained
				// for CNF: if there is {A,B} and {A} we may remove {A,B}
				// (A || B) && A is equivalent to A
				Set<Set<Term>> tidyResOuterSet = new HashSet<Set<Term>>(resOuterSet);
				for (Set<Term> resInnerSet : resOuterSet) {
					if (!mServices.getProgressMonitorService().continueProcessing()) {
						throw new ToolchainCanceledException();
					}
					if (tidyResOuterSet.contains(resInnerSet)) {
						Iterator<Set<Term>> it = tidyResOuterSet.iterator();
						while (it.hasNext()) {
							Set<Term> tidyResInnerSet = it.next();
							if (tidyResInnerSet != resInnerSet && 
									tidyResInnerSet.containsAll(resInnerSet)) {
								it.remove();
							}
						}
					}
				}
				Term[] resInnerTerms = new Term[tidyResOuterSet.size()];
				int i = 0;
				for (Set<Term> resInnerSet : tidyResOuterSet) {
					resInnerTerms[i] = 
							innerConnective(m_Script, resInnerSet.toArray(new Term[0]));
					i++;
				}
				assert i==resInnerTerms.length;
				result = outerConnective(m_Script, resInnerTerms);
			} else if (functionSymbolName.equals(outerConnectiveSymbol())) {
				result = outerConnective(m_Script, newArgs);
			} else {
				throw new AssertionError();
			}
			setResult(result);
		}
		
		/**
		 * Add inputInner to all subsets of resOuterSet.
		 * Additional Optimization:
		 * In a preprocessing step, we check if the singleton {inputInner} is
		 * already an element of resOuter Set. If this is the case we do not
		 * add anything and remove all sets from resOutSet but {inputInner}.
		 * This optimization (in terms of CNF) corresponds to the fact
		 * that
		 * (A /\ (B_1 \/ B2) /\ (C_1 \/ C2))  \/ A
		 * and 
		 * A
		 * are equivalent.
		 */
		private void product(HashSet<Set<Term>> resOuterSet, Term inputInner) {
			Set<Term> singleton = Collections.singleton(inputInner);
			if (resOuterSet.contains(singleton)) {
				resOuterSet.retainAll(Collections.singleton(singleton));
			} else {
				for (Set<Term> outer : resOuterSet) {
					// for efficiency we reuse the old set in this case
					outer.add(inputInner);
				}
			}
		}
		
		/**
		 * Take inputOuters.lenth copies of oldResOuterSet. In each copy we
		 * put in each set an element of inputOuters.
		 * 
		 * Additional Optimization:
		 * In a preprocessing step, we check if there is an element x in 
		 * inputOuters, such that the singleton {x} is in oldResOuter set.
		 * If this is the case, 
		 * - we remove x from inputOuters, 
		 * - we remove {x} from oldResOuterSet, and
		 * - we add {x} to resOuterSet
		 * This optimization (in terms of CNF) corresponds to the fact
		 * that
		 * (A /\ (B_1 \/ B2) /\ (C_1 \/ C2))  \/ (A /\ D)
		 * and 
		 * (A /\ (B_1 \/ B2 \/ D) /\ (C_1 \/ C2 \/ D))
		 * are equivalent.
		 *  
		 */
		private void product(HashSet<Set<Term>> resOuterSet,
				HashSet<Set<Term>> oldResOuterSet, Set<Term> inputOuters) {
			// above mentioned preprocessing
			Iterator<Set<Term>> it = oldResOuterSet.iterator();
			while (it.hasNext()) {
				Set<Term> oldResOuter = it.next();
				if (oldResOuter.size() == 1) {
					Term oldResOuterSingletonElement = oldResOuter.iterator().next();
					if (inputOuters.contains(oldResOuterSingletonElement)) {
						inputOuters.remove(oldResOuterSingletonElement);
						resOuterSet.add(oldResOuter);
						it.remove();
					}
				}
			}
			// for CNF: we iterate over all disjuncts
			for (Term inputOuter : inputOuters) {
				for (Set<Term> oldOuter : oldResOuterSet) {
					HashSet<Term> newOuter = new HashSet<Term>(oldOuter);
					newOuter.add(inputOuter);
					resOuterSet.add(newOuter);
				}
			}
		}

	}

}
