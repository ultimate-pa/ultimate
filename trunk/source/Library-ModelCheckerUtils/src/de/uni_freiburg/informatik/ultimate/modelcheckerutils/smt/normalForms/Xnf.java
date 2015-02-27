package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Literal.Polarity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.XJunction.AtomAndNegationException;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

/**
 * Common abstract superclass of Cnf and Dnf.
 * In order to understand the variable names and the documentation
 * replace "outer" by "conjunct" and "inner" by "disjunct" for CNF, and
 * replace "outer" by "disjunct" and "inner" by "conjunct" for DNF.
 * In documentation we use the Greek letter iota 'ι' to denote the inner 
 * connective and we use the Greek letter omikron 'o' to denote the outer
 * connective.
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
		
		public abstract Term innerConnective(Script script, List<Term> params);
		public abstract Term outerConnective(Script script, List<Term> params);
		
//		public abstract Term[] getInnerJuncts(Term term);
		public abstract Term[] getOuterJuncts(Term term);
		
		@Override
		public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
			String functionSymbolName = appTerm.getFunction().getName();
			Term result;
			if (functionSymbolName.equals(innerConnectiveSymbol())) {
				// case where the connective of the formula is inner connective
				// of the normal form.
//				System.out.println("DAG size " + (new DagSizePrinter(Util.and(m_Script, newArgs))));
				Term[] resOuterJuncts = applyDistributivityAndOr(newArgs);
				result = outerConnective(m_Script, Arrays.asList(resOuterJuncts));
			} else if (functionSymbolName.equals(outerConnectiveSymbol())) {
				result = outerConnective(m_Script, Arrays.asList(newArgs));
			} else {
				throw new AssertionError();
			}
			setResult(result);
		}
		
		
		/**
		 * Uses Distributivity to transform an innerJunction (given as an array
		 * of innerJuncts) to an equivalent outerJunction (given as an array of 
		 * outerJuncts).
		 * E.g., ((A o B) ι (C ο D)) is transformed to 
		 * (A ι C) o (A ι D) o (B ι C) o (B ι D)
		 * @param inputInnerJunction
		 * @return
		 */
		private Term[] applyDistributivityAndOr(Term[] inputInnerJunction) {
//			System.out.println("InnerJuncts " + inputInnerJunction.length);
			
			
			

			XJunction elementsOfSingletonOuterJuncts = new XJunction();
			
			Set<XJunction> innerJunctionOfOuterJunctions = new HashSet<>();
			for (Term inputInnerJunct : inputInnerJunction) {
				Term[] inputOuterJunction = getOuterJuncts(inputInnerJunct);
				try {
					innerJunctionOfOuterJunctions.add(new XJunction(inputOuterJunction));
				} catch (AtomAndNegationException e) {
					// do nothing - outerJunction is true/false
				}
			}
			try {
				innerJunctionOfOuterJunctions = resolutionLike(elementsOfSingletonOuterJuncts, innerJunctionOfOuterJunctions);
			} catch (AtomAndNegationException e) {
				// result is true/false
				return new Term[0];
			}
			
			if (innerJunctionOfOuterJunctions.size() > 5) {
				System.out.println("exponential blowup for input size " + innerJunctionOfOuterJunctions.size());
			}
			// result outerJunction of innerJunction e.g. for CNF this is a 
			// conjunction of disjunctions
			Set<XJunction> resOuterJunction = new HashSet<XJunction>();
			// first we add the empty innerJunction
			// for CNF this is empty disjunction (which is equivalent to false)
			XJunction initialInnerJunction = new XJunction();
			resOuterJunction.add(initialInnerJunction);
			for (XJunction inputOuterJunction : innerJunctionOfOuterJunctions) {
				// we iterate over each innerJunct of the input 
//				Term[] inputOuterJunction = getOuterJuncts(inputInnerJunct);
//				XJunction inputOuters = BooleanTermWithPolarity.computePolarityMap(inputOuterJunction);
//				if (inputOuters == null) {
//					// for CNF: inputOuters equivalent to false
//					// we do not modify resOuterJunction
//				} else {
					resOuterJunction = product(resOuterJunction, inputOuterJunction);
//				}
			}
			// remove all sets for which a strict subset is contained
			// for CNF: if there is {A,B} and {A} we may remove {A,B}
			// (A || B) && A is equivalent to A
			Set<XJunction> tidyResOuterSet = new HashSet<XJunction>(resOuterJunction);
			for (XJunction resInnerSet : resOuterJunction) {
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(this.getClass());
				}
				if (tidyResOuterSet.contains(resInnerSet)) {
					Iterator<XJunction> it = tidyResOuterSet.iterator();
					while (it.hasNext()) {
						XJunction tidyResInnerSet = it.next();
						if (tidyResInnerSet != resInnerSet && 
								tidyResInnerSet.entrySet().containsAll(resInnerSet.entrySet())) {
							it.remove();
						}
					}
				}
			}
			Term[] resInnerTerms = new Term[tidyResOuterSet.size()];
			int i = 0;
			for (XJunction resInnerSet : tidyResOuterSet) {
				XJunction withSingletons;
				try {
					withSingletons = XJunction.disjointUnion(resInnerSet, elementsOfSingletonOuterJuncts);
				} catch (AtomAndNegationException e) {
					throw new AssertionError("atom and negation? xjunction should have been removed");
				}
				resInnerTerms[i] = 
						innerConnective(m_Script, withSingletons.toTermList(m_Script));
				i++;
			}
			assert i==resInnerTerms.length;
			return resInnerTerms;
		}
		
		public Set<XJunction> resolutionLike(XJunction innerJunction, Set<XJunction> innerJunctionOfOuterJunctions) throws AtomAndNegationException {
			while (true) {
				boolean modified = moveSingletons(innerJunction, innerJunctionOfOuterJunctions);
				if (!modified) {
					return innerJunctionOfOuterJunctions;
				}
				Set<XJunction> newinnerJunctionOfOuterJunctions = modify(innerJunction, innerJunctionOfOuterJunctions);
				if (newinnerJunctionOfOuterJunctions == innerJunctionOfOuterJunctions) {
					return innerJunctionOfOuterJunctions;
				} else {
					innerJunctionOfOuterJunctions = newinnerJunctionOfOuterJunctions;
				}
			}
			
			
			
		}
		private Set<XJunction> modify(XJunction innerJunction,
				Set<XJunction> innerJunctionOfOuterJunctions) {
			HashSet<XJunction> newi = new HashSet<XJunction>();
			boolean modified = false;
			for (XJunction xjunction : innerJunctionOfOuterJunctions) {
				boolean xjunctionNotAddedOrModified = 
						addIfNoAtomContained(innerJunction, newi, xjunction); 
				modified |= xjunctionNotAddedOrModified;
			}
			if (modified) {
				return newi;
			} else {
				return innerJunctionOfOuterJunctions;
			}
		}
		/**
		 * Add xjunction to set if xjunction and innerJunction are disjoint.
		 * We mean disjoint in the sense that no atom (with same polarity) is
		 * contained in both.
		 * Additionally, we remove from xjunction all atoms that occur negated
		 * in innerJunction. 
		 * @return true iff xjunction was modified before adding or not added
		 * at all.
		 */
		private boolean addIfNoAtomContained(XJunction innerJunction,
				HashSet<XJunction> set, XJunction xjunction) {
			boolean modified = false;
			for (Entry<Term, Polarity> literal : innerJunction.entrySet()) {
				if (xjunction.contains(literal.getKey(), literal.getValue())) {
					// do not add
					modified = true;
					return modified;
				} else if (xjunction.containsNegation(literal.getKey(), literal.getValue())) {
					// remove negation and add to result
					xjunction.remove(literal.getKey());
					modified = true;
				}
			}
			set.add(xjunction);
			return modified;
		}
		private boolean moveSingletons(XJunction innerJunction,
				Set<XJunction> innerJunctionOfOuterJunctions)
				throws AtomAndNegationException {
			boolean someSingletonMoved = false;
			Iterator<XJunction> it = innerJunctionOfOuterJunctions.iterator();
			while (it.hasNext()) {
				XJunction outerJunction = it.next();
				if (outerJunction.size() == 1) {
					Entry<Term, Polarity> singleton = outerJunction.entrySet().iterator().next();
					innerJunction.add(singleton.getKey(), singleton.getValue());
					someSingletonMoved = true;
					it.remove();
				}
			}
			return someSingletonMoved;
		}
		
//		/**
//		 * Given an outerJunctionOfInnerJunctions, add atom to each 
//		 * innerJunction.
//		 * Optimization 1:
//		 * If an innerJunction already contains "(not atom)" we drop this
//		 * innerJunction.
//		 * This optimization corresponds to the fact that
//		 *     (((not A) ι B) o (C_1 ι C2)) ι A
//		 * and
//		 *     (C_1 ι C2 ι A)
//		 * are equivalent.
//		 * 
//		 * Optimization 2:
//		 * We check if the singleton {atom} is an an outerJunct of the 
//		 * outerJunctionOfInnerJunctions Set. 
//		 * If this is the case we do not add anything and instead remove all
//		 * other innerJunctions from the outerJunctionOfInnerJunctions Set.
//		 * This optimization corresponds to the fact that
//		 *     (A o (B_1 ι B2) o (C_1 ι C2)) ι A
//		 * and 
//		 *     A
//		 * are equivalent.
//		 */
//		private void product(HashSet<XJunction> outerJunctionOfInnerJunctions, BooleanTermWithPolarity atom) {
//			XJunction singleton = Collections.singletonMap(atom.getTerm(), atom.getPolarity());
//			if (outerJunctionOfInnerJunctions.contains(singleton)) {
//				// case where outerJunction contains already the singleton
//				// {atom} (see Optimization 2 above)
//				outerJunctionOfInnerJunctions.retainAll(Collections.singleton(singleton));
//				assert outerJunctionOfInnerJunctions.size() == 1;
//			} else {
//				// for efficiency we reuse the old set in this case
//				Iterator<XJunction> it = outerJunctionOfInnerJunctions.iterator();
//				while (it.hasNext()) {
//					// add atom to innerJunction. If is was already contained
//					// with a different polarity we remove this innerJunction
//					// (see Optimization 1 above)
//					XJunction innerJunction = it.next();
//					boolean containedWithOppositePolarity = 
//							BooleanTermWithPolarity.checkForNegation(innerJunction, atom.getTerm(), atom.getPolarity());
//					if (containedWithOppositePolarity) {
//						it.remove();
//					} else {
//						innerJunction.put(atom.getTerm(), atom.getPolarity());
//					}
//				}
//			}
//		}
		
		
		/**
		 * Given an outerJunctionOfInnerJunctions and a set of atoms.
		 * We return an outerJunction of innerJunctions that is obtained by 
		 * taking atoms.size() copies of the input. In each copy we add 
		 * different atom.
		 * Formally, given an outerJunctionOfInnerJunctions
		 *     o_{i} ι_{i_k} X_{i_k}
		 * and a set of atoms
		 *     a_1,...,a_m
		 * we return the following outerJunction of innerJunctions.
		 *     o_{j=1,...,m} o_{i} ι_{i_k} (X_{i_k} ∪ {a_j})
		 * The result is a new HashSet, however both inputs are modified.
		 * The result is not exactly the set defined above but an equivalent
		 * set (equivalent wrt. Boolean algebra), because we apply the following
		 * Optimizations.
		 *  
		 * Optimization 1:
		 * If an innerJunction already contains "(not atom)" we drop this
		 * innerJunction.
		 * This optimization corresponds to the fact that
		 *     (((not A) ι B) o (C_1 ι C2)) ι A
		 * and
		 *     (C_1 ι C2 ι A)
		 * are equivalent.
		 * 
		 * Optimization 2:
 		 * In a preprocessing step, we check if there is an element x in 
		 * atoms, such that the singleton {x} is in an outerJunct.
		 * If this is the case, 
		 * - we remove x from atoms, 
		 * - we remove {x} from outerJunctionOfInnerJunctions, and
		 * - we add {x} to the result.
		 * This optimization corresponds to the fact that
		 *     (A o (B_1 ι B2) o (C_1 ι C2))  ι (A o D)
		 * and 
		 *     (A o (B_1 ι B2 ι D) o (C_1 ι C2 ι D))
		 * are equivalent.
		 */
		private Set<XJunction> product(Set<XJunction> outerJunctionOfInnerJunctions, XJunction atoms) {
//			System.out.println("Atoms " + atoms.size());
			Set<XJunction> result = new HashSet<XJunction>();
			// above mentioned preprocessing
			Iterator<XJunction> it = outerJunctionOfInnerJunctions.iterator();
			while (it.hasNext()) {
				XJunction outerJunct = it.next();
				if (outerJunct.size() == 1) {
					Entry<Term, Polarity> singletonInnerJunction = outerJunct.entrySet().iterator().next();
					Term singletonInnerJunctionTerm = singletonInnerJunction.getKey();
					Polarity singletonInnerJuntionPolarity = singletonInnerJunction.getValue();
					atoms.getPolarity(singletonInnerJunctionTerm);
					if (atoms.getPolarity(singletonInnerJunctionTerm) == singletonInnerJuntionPolarity) {
						// element with same polarization is contained
						atoms.remove(singletonInnerJunctionTerm);
						result.add(outerJunct);
						it.remove();
					}
				}
			}
			// for CNF: we iterate over all disjuncts
			for (Entry<Term, Polarity> atom : atoms.entrySet()) {
				int loopCounter = 0;
				for (XJunction innerJunction : outerJunctionOfInnerJunctions) {
					if (innerJunction.containsNegation(atom.getKey(), atom.getValue())) {
						// the element with the other polarization was already
						// contained. We omit new Outer since it is trivial
						// In terms of CNF: we have a conjunct of the
						// form (A \/ ...) and we added (not A) hence this 
						// conjunct is equivalent to true and we should remove 
						// it from the conjunction.
					} else {
						XJunction newOuter = new XJunction(innerJunction);
						try {
							newOuter.add(atom.getKey(), atom.getValue());
						} catch (AtomAndNegationException e) {
							throw new AssertionError("checked before");
						}
						result.add(newOuter);
					}
					
					if (loopCounter == 10000) {
//						System.out.println("Outer size " + result.size());
						if (!mServices.getProgressMonitorService().continueProcessing()) {
							throw new ToolchainCanceledException(this.getClass());
						} else {
							loopCounter = 0; 
						}
					} 
					loopCounter++;

				}
			}
			return result;
		}

	}
	
	
	class XJunctionPosetMinimalElements {
		private final Set<XJunction> m_Elements = new HashSet<XJunction>();
		
		
		public void add(XJunction xjunction) {
			Iterator<XJunction> it = m_Elements.iterator();
			while (it.hasNext()) {
				XJunction existing = it.next();
				if(existing.isSubset(xjunction)) {
					// add nothing
					return;
				}
				if(xjunction.isSubset(existing)) {
					it.remove();
				}
			}
			m_Elements.add(xjunction);
		}


		public Set<XJunction> getElements() {
			return m_Elements;
		}
		
		public int size() {
			return m_Elements.size();
		}
		
		
	}

}
