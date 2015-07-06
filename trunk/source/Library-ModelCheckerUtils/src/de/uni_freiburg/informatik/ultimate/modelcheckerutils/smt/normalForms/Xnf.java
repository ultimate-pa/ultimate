/*
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Model Checker Utils Library.
 *
 * The ULTIMATE Model Checker Utils Library is free software: you can 
 * redistribute it and/or modify it under the terms of the GNU Lesser General 
 * Public License as published by the Free Software Foundation, either 
 * version 3 of the License, or (at your option) any later version.
 *
 * The ULTIMATE Model Checker Utils Library is distributed in the hope that it
 * will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty 
 * of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Model Checker Utils Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Model Checker Utils Library, or any covered work, 
 * by linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE Model Checker Utils Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
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
	
	public Xnf(Script script, IUltimateServiceProvider services, 
			IFreshTermVariableConstructor freshTermVariableConstructor) {
		super(script, services, freshTermVariableConstructor);
	}
	
	protected abstract class XnfTransformerHelper extends NnfTransformerHelper {

		protected XnfTransformerHelper(IUltimateServiceProvider services) {
			super(services);
		}
		public abstract String innerConnectiveSymbol();
		public abstract String outerConnectiveSymbol();
		
		public abstract String innerJunctionName();
		public abstract String outerJunctionName();
		
		public abstract Term innerConnective(Script script, List<Term> params);
		public abstract Term outerConnective(Script script, List<Term> params);
		
		public abstract Term[] getOuterJuncts(Term term);
		
		@Override
		public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
			String functionSymbolName = appTerm.getFunction().getName();
			Term result;
			if (functionSymbolName.equals(innerConnectiveSymbol())) {
				// case where the connective of the formula is inner connective
				// of the normal form.
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
		 * In order to keep the result small optimizations are applied.
		 * @param inputInnerJunction
		 * @return
		 */
		private Term[] applyDistributivityAndOr(Term[] inputInnerJunction) {

			ResultInnerJunctions first;
			{
				Set<XJunction> innerJunctionOfOuterJunctions = 
						convertInnerJunctionOfOuterJunctionsToSet(inputInnerJunction);
				try {
					first = new ResultInnerJunctions(innerJunctionOfOuterJunctions);
					innerJunctionOfOuterJunctions = null;
				} catch (AtomAndNegationException e1) {
					// innerJunctionOfOuterJunctions contains the singleton {φ}
					// and the singleton {¬φ}.
					// Hence the result is equivalent to the annihilator of the 
					// innerJunction resp. the neutral element of the 
					// outerJunction (true for ∧, false for ∨)
					return new Term[0];
				}
			}
			
			int inputSize = first.numberOfUnprocessedOuterJunctions();
			if ( inputSize > 5) {
				m_Logger.warn("expecting exponential blowup for input size " + inputSize);
			}
			
			// iteratively apply distributivity until we have a set of innerJunctions.
			Set<XJunction> resOuterJunction = new HashSet<XJunction>();
			Stack<ResultInnerJunctions> todoStack = new Stack<ResultInnerJunctions>();
			todoStack.add(first);
			while (!todoStack.isEmpty()) {
				ResultInnerJunctions top = todoStack.pop();
				if (top.isProcessedToInnerJunction()) {
					resOuterJunction.add(top.getInnerJunction());
				} else {
					todoStack.addAll(top.processOneOuterJunction());
				}
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(this.getClass(),
							"XNF transformer was applied to  " + inputSize + " " + innerJunctionName());
				}
			}
			
			boolean timeConsumingSimplification = (resOuterJunction.size() > 5000);
			if (timeConsumingSimplification) {
				m_Logger.warn("Simplifying " + outerJunctionName() + " of " 
						+ resOuterJunction.size() + " " + innerJunctionName() + 
						"s. " + "This might take some time...");
			}
			
			// Simplify by keeping only minimal (with respect to set inclusion)
			// outerJunctions.
			XJunctionPosetMinimalElements pme = new XJunctionPosetMinimalElements();
			for (XJunction resInnerSet : resOuterJunction) {
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(this.getClass(),
							"XNF transformer was simplifying " + resOuterJunction.size() 
							+ " " + innerJunctionName() + "s. ");
				}
				pme.add(resInnerSet);
			}
			
			if (timeConsumingSimplification) {
				m_Logger.info("Simplified to " + outerJunctionName() + " of " 
						+ pme.getElements().size() + " " + innerJunctionName() + 
						"s. ");
			}
			
			// Construct terms.
			Term[] resInnerTerms = new Term[pme.getElements().size()];
			int i = 0;
			for (XJunction resInnerSet : pme.getElements()) {
				resInnerTerms[i] = innerConnective(m_Script, resInnerSet.toTermList(m_Script));
				i++;
			}
			assert i==resInnerTerms.length;
			return resInnerTerms;
		}
		
		/**
		 * Convert an innerJunction of outerJunctions given as an array of terms
		 * into a Set of XJunctions. 
		 */
		private Set<XJunction> convertInnerJunctionOfOuterJunctionsToSet(
				Term[] inputInnerJunction) {
			Set<XJunction> result = new HashSet<>();
			for (Term inputInnerJunct : inputInnerJunction) {
				Term[] inputOuterJunction = getOuterJuncts(inputInnerJunct);
				try {
					result.add(new XJunction(inputOuterJunction));
				} catch (AtomAndNegationException e) {
					// do nothing, we omit this outerJunction because it is
					// equivalent to the neutral element of the inner connective
					// (true for ∧, false for ∨)
				}
			}
			return result;
		}
		
		/**
		 * Represents a an innerJunction of outerJunctions using
		 * <ul> 
		 * <li> one innerJunction given as an XJunction (m_InnerJuncts) and
		 * <li> one innerJunction of outerJunctions given as a set of 
		 * XJunctions (m_UnprocessedInnerJunctionOfOuterJunctions).
		 * </ul>
		 *    (m_InnerJuncts ι (outerJunction_1 ι ... ι outerJunction_n))
		 * This class can be used to successively apply distributivity to
		 * get rid of the outerJunctions. Therefore objects of this class
		 * are split into a set of such objects, one for each outerJunct.
		 * 
		 * @author Matthias Heizmann
		 *
		 */
		private class ResultInnerJunctions {
			private final XJunction m_InnerJuncts;
			private final Set<XJunction> m_UnprocessedInnerJunctionOfOuterJunctions;
			
			public ResultInnerJunctions(Set<XJunction> innerJunctionOfOuterJunctions) throws AtomAndNegationException {
				XJunction innerJuncts = new XJunction(); 
				m_UnprocessedInnerJunctionOfOuterJunctions = moveOutwardsAbsorbeAndMpsimplify(innerJuncts, innerJunctionOfOuterJunctions);
				m_InnerJuncts = innerJuncts;
			}
			
			public ResultInnerJunctions(XJunction innerJuncts, Set<XJunction> innerJunctionOfOuterJunctions) throws AtomAndNegationException {
				XJunction newInnerJuncts = new XJunction();
				m_UnprocessedInnerJunctionOfOuterJunctions = moveOutwardsAbsorbeAndMpsimplify(newInnerJuncts, innerJunctionOfOuterJunctions);
				m_InnerJuncts = XJunction.disjointUnion(innerJuncts, newInnerJuncts);
			}
			
			public boolean isProcessedToInnerJunction() {
				return m_UnprocessedInnerJunctionOfOuterJunctions.isEmpty();
			}
			
			public int numberOfUnprocessedOuterJunctions() {
				return m_UnprocessedInnerJunctionOfOuterJunctions.size();
			}
			
			public XJunction getInnerJunction() {
				return m_InnerJuncts;
			}
			
			public List<ResultInnerJunctions> processOneOuterJunction() {
				Iterator<XJunction> it = m_UnprocessedInnerJunctionOfOuterJunctions.iterator();
				XJunction next = it.next();
				it.remove();
				ArrayList<ResultInnerJunctions> result = new ArrayList<>(next.size());
				for (Entry<Term, Polarity> entry : next.entrySet()) {
					XJunction singletonInnerJunct = new XJunction(entry.getKey(), entry.getValue());
					Set<XJunction> innerJunctionOfOuterJunctions = new HashSet<XJunction>(m_UnprocessedInnerJunctionOfOuterJunctions);
					innerJunctionOfOuterJunctions.add(singletonInnerJunct);
					XJunction innerJunctions = new XJunction(m_InnerJuncts);
					try {
						ResultInnerJunctions rij = new ResultInnerJunctions(innerJunctions, innerJunctionOfOuterJunctions);
						result.add(rij);
					} catch (AtomAndNegationException e) {
						// omit this ResultInnerJunctions it is equivalent to true/false
					}
				}
				return result;
			}
			
			/**
			 * Given an innerJunction and an innerJunction of outerJunctions, we 
			 * consider this an an innerJunction
			 * (innerJunction ι (outerJunction_1 ι ... ι outerJunction_n))
			 * and move as many elements as possible to innerJunction by applying 
			 * equivalence transformations.
			 * 
			 * @param innerJunction input and output of this method. This method
			 * adds new elements to this XJunction.
			 * @param innerJunctionOfOuterJunctions input of this method, but also
			 * used to store intermediate data. It is modified and should not be 
			 * used by the caller after calling this method.
			 * However the XJunction contained in this set are not modified.
			 * @return and innerJunction of outerJunction that is together with
			 * the modified innerJunction equivalent to the input.
			 * @throws AtomAndNegationException thrown if we detect that the input
			 * is equivalent to the annihilating element of the inner connective
			 */
			private Set<XJunction> moveOutwardsAbsorbeAndMpsimplify(
					XJunction innerJunction, 
					Set<XJunction> innerJunctionOfOuterJunctions) throws AtomAndNegationException {
				while (true) {
					boolean modified = moveSingletonsOutwards(innerJunction, innerJunctionOfOuterJunctions);
					if (!modified) {
						return innerJunctionOfOuterJunctions;
					}
					Set<XJunction> newinnerJunctionOfOuterJunctions = applyAbsorbeAndMpsimplify(innerJunction, innerJunctionOfOuterJunctions);
					if (newinnerJunctionOfOuterJunctions == innerJunctionOfOuterJunctions) {
						return innerJunctionOfOuterJunctions;
					} else {
						innerJunctionOfOuterJunctions = newinnerJunctionOfOuterJunctions;
					}
				}
			}

			/**
			 * Remove from innerJunctionOfOuterJunctions all XJunctions that are
			 * singletons and move their elements to innerJunction.
			 * @param innerJunction is modified and used as input and output of 
			 * this method
			 * @param innerJunctionOfOuterJunctions is modified and input and 
			 * output of this method
			 * @return true iff innerJunctionOfOuterJunctions contained a singleton
			 * (note that if the result is false this means especially that the
			 * inputs were not modified)
			 * @throws AtomAndNegationException the resulting innerJunction would
			 * be equivalent to the annihilating element of the inner connective.
			 */
			private boolean moveSingletonsOutwards(XJunction innerJunction,
					Set<XJunction> innerJunctionOfOuterJunctions)
							throws AtomAndNegationException {
				boolean someSingletonContained = false;
				Iterator<XJunction> it = innerJunctionOfOuterJunctions.iterator();
				while (it.hasNext()) {
					XJunction outerJunction = it.next();
					if (outerJunction.size() == 1) {
						Entry<Term, Polarity> singleton = outerJunction.entrySet().iterator().next();
						innerJunction.add(singleton.getKey(), singleton.getValue());
						someSingletonContained = true;
						it.remove();
					}
				}
				return someSingletonContained;
			}



			/**
			 * Given an innerJunction and an innerJunction of outerJunctions, we 
			 * consider this an an innerJunction
			 * (innerJunction ι (outerJunction_1 ι ... ι outerJunction_n))
			 * and simplify the innerJunction of outerJunctions by applying two
			 * simplification rules.
			 * <ul>
			 *  <li> 1. Absorption. If innerJunction and outerJunction_i share
			 *  a common element, we drop outerJunction_i from the innerJunction
			 *  of outerJuncts.
			 *  <li> 2. Mpsimplify. If innerJunction contains a formula φ and one
			 *  outerJunction of outerJunction_i is ¬φ we remove this outerJunction
			 *  from outerJunction_i.
			 * </ul>
			 * @param innerJunction above mentioned innerJunction, not modified by 
			 * this methods
			 * @param innerJunctionOfOuterJunctions above mentioned innerJunction 
			 * of outerJunctions, not modified by this method
			 * @return innerJunction of outerJunctions which is simplified with 
			 * respect to innerJunction as mentioned above. If no simplification
			 * was possible innerJunctionOfOuterJunctions (same Object) is returned
			 * otherwise a new HashSet is returned.
			 */
			private Set<XJunction> applyAbsorbeAndMpsimplify(XJunction innerJunction,
					Set<XJunction> innerJunctionOfOuterJunctions) {
				HashSet<XJunction> newInnerJunctionOfOuterJunctions = new HashSet<XJunction>();
				boolean modified = false;
				for (XJunction outerJunction : innerJunctionOfOuterJunctions) {
					XJunction newOuterJunction = applyAbsorbeAndMpsimplify(innerJunction, outerJunction);
					if (newOuterJunction == null) {
						// do not add, absorbed by innerJunction
						modified = true;
					} else if (outerJunction == newOuterJunction) {
						// nothing was simplified
						newInnerJunctionOfOuterJunctions.add(newOuterJunction);
					} else {
						// some elements were removed
						assert (outerJunction.size() > newOuterJunction.size());
						newInnerJunctionOfOuterJunctions.add(newOuterJunction);
					}
				}
				if (modified) {
					return newInnerJunctionOfOuterJunctions;
				} else {
					return innerJunctionOfOuterJunctions;
				}
			}

			/**
			 * Given an innerJunction and an outerJunction, we consider this as an
			 * inner Junction
			 *     (innerJunction ι outerJunction)
			 * and simplify outerJunction with respect to innerJunction.
			 * If innerJunction and outerJunction share a common literal we 
			 * simplify outerJunction to the neutral element of the innerJunction
			 * (absorption) and return null to indicate that.
			 * If there is a literal in outerJunction that occurs with the opposite
			 * polarity in innerJunction, we remove it from the outerJunction
			 * (mpsimplify, reminiscent to modus ponens). In fact, outerJunction
			 * is never modified, if we have to modify it, we return a new XJunction
			 * instead. If we do not have to modify it, we return the input
			 * outerJunction.
			 */
			private XJunction applyAbsorbeAndMpsimplify(XJunction innerJunction,
					XJunction outerJunction) {
				XJunction resultOuterJunction = outerJunction;
				for (Entry<Term, Polarity> literal : innerJunction.entrySet()) {
					if (outerJunction.contains(literal.getKey(), literal.getValue())) {
						return null;
					} else if (outerJunction.containsNegation(literal.getKey(), literal.getValue())) {
						// remove negation
						if (resultOuterJunction == outerJunction) {
							resultOuterJunction = new XJunction(outerJunction);
						}
						resultOuterJunction.remove(literal.getKey());
					}
				}
				return resultOuterJunction;
			}
		}
		
		
		/**
		 * Represents a Set of XJunction with the following property.
		 * The set cannot contain two elements that are comparable via 
		 * inclusion.
		 * Whenever we add an element xjunction_new such that for some existing
		 * xjunction xjunction_old the inclusion 
		 *     xjunction_old ⊆ xjunction_new
		 * the new element xjunction_new is discarded.
		 * Whenever we add an element xjunction_new we remove all existing
		 * xjunctions xjunction_old for which the inclusion
		 *     xjunction_new ⊆ xjunction_old
		 * hols.
		 * 
		 * @author Matthias Heizmann
		 *
		 */
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
}
