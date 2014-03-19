package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.normalForms;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.OperationCanceledException;

/**
 * Common abstract superclass of Cnf and Dnf. 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public abstract class Xnf extends Nnf {

	public Xnf(Script script) {
		super(script);
	}
	
	protected abstract class XnfTransformerHelper extends NnfTransformerHelper {

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
				HashSet<Term> resOuterTerms = new HashSet<Term>();
				// for CNF we start with the empty disjunction (which is false)
				resOuterTerms.add(m_Script.term(innerConnectiveNeutralElement()));
				resOuterSet.add(new HashSet<Term>());
				for (Term inputInner : newArgs) {
					//e.g. for CNF we iterate over each disjunct of the input
					HashSet<Term> oldResOuterTerms = resOuterTerms;
					HashSet<Set<Term>> oldResOuterSet = resOuterSet;
					resOuterTerms = new HashSet<Term>();
					resOuterSet = new HashSet<Set<Term>>();
					if ((inputInner instanceof ApplicationTerm) && 
							((ApplicationTerm) inputInner).getFunction().getName().equals(outerConnectiveSymbol())) {
						// for CNF: if this input conjunct is a disjunction we
						// have a construct a copy of each result disjunction
						// and add this disjunct
						Term[] inputOuters = ((ApplicationTerm) inputInner).getParameters();
						// for CNF: we iterate over all disjuncts
						for (Term inputOuter : inputOuters) {
							for (Term oldOuter : oldResOuterTerms) {
								resOuterTerms.add(
										innerConnective(m_Script, oldOuter, inputOuter));
							}
							for (Set<Term> oldOuter : oldResOuterSet) {
								HashSet<Term> newOuter = new HashSet<Term>(oldOuter);
								newOuter.add(inputOuter);
								resOuterSet.add(newOuter);
							}
						}
					} else {
						// for CNF if this input conjunct is an atom have to add
						// this atom to each result disjunction
						for (Term oldOuter : oldResOuterTerms) {
							resOuterTerms.add(
									innerConnective(m_Script, oldOuter, inputInner));
						}
						for (Set<Term> oldOuter : oldResOuterSet) {
							// for efficiency we reuse the old set in this case
							Set<Term> newOuter = oldOuter;
							newOuter.add(inputInner);
							resOuterSet.add(newOuter);
						}
					}
				}
				// remove all sets for which a strict subset is contained
				// for CNF: if there is {A,B} and {A} we may remove {A,B}
				// (A || B) && A is equivalent to A
				Set<Set<Term>> tidyResOuterSet = new HashSet<Set<Term>>(resOuterSet);
				for (Set<Term> resInnerSet : resOuterSet) {
					if (!UltimateServices.getInstance().continueProcessing()) {
						throw new OperationCanceledException();
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

	}

}
