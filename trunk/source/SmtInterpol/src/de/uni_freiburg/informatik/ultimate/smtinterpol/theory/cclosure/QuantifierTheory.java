/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.ArrayInstantiationUnifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.ArrayYieldTrigger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.TriggerData;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.YieldTrigger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.QuantifiedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;

public class QuantifierTheory implements ITheory {

	private static class TriggerPair {
		CCTrigger t1, t2;

		public TriggerPair(CCTrigger t1, CCTrigger t2) {
			this.t1 = t1;
			this.t2 = t2;
		}
	}

	private int mnumqstotal = 0;
	private int mnumqs = 0;
	private int mnumqbtotal = 0;
	private int mnumqb = 0;
	private int skolemcounter = 0;
	private HashMap<CCTerm[], CCTrigger> m_TriggerTrees = 
		new HashMap<CCTerm[], CCTrigger>();

	private CClosure mengine;

	private static final int MAX_INSTS_PER_ROUND = 100;
	
	public QuantifierTheory(CClosure engine) {
		mengine = engine;
//		mengine.ematchingActive = true;
	}

	@Override
	public void backtrackLiteral(Literal literal) {
		if (literal instanceof QuantifiedAtom) {
			++mnumqb;
			++mnumqbtotal;
			QuantifiedAtom qa = (QuantifiedAtom) literal;
			for (TriggerData td : qa.getTriggers())
				remove(td);
		}
	}

	@Override
	public Clause checkpoint() {
//		boolean goon = true;
//		while (goon && mengine.curinsts == 0)
//			goon = mengine.processTriggers(MAX_INSTS_PER_ROUND);
//		mengine.curinsts = 0;
		return null;
	}

	@Override
	public Clause computeConflictClause() {
		// TODO Here, we could implement Quantifier Model Checking...
		return checkpoint();
	}

	@Override
	public void decreasedDecideLevel(int currentDecideLevel) {
	}

	@Override
	public void dumpModel(Logger logger) {
	}

	@Override
	public Literal getPropagatedLiteral() {
		return null;
	}

	@Override
	public Literal getSuggestion() {
		return null;
	}

	@Override
	public Clause getUnitClause(Literal literal) {
		throw new InternalError("Should not be called!");
	}

	@Override
	public void increasedDecideLevel(int currentDecideLevel) {
	}

	@Override
	public void printStatistics(Logger logger) {
		logger.info("QS: " + mnumqs + " / " + mnumqstotal);
		logger.info("QB: " + mnumqb + " / " + mnumqbtotal);
		logger.info("SK: " + skolemcounter);
	}

	@Override
	public void restart(int iteration) {
	}

	@Override
	public Clause setLiteral(Literal literal) {
		if (literal instanceof QuantifiedAtom) {
			++mnumqs;
			++mnumqstotal;
			QuantifiedAtom qa = (QuantifiedAtom) literal;
			TriggerData[] trigs = qa.getTriggers();
			if (trigs != null) {
				for (TriggerData td : trigs)
					add(td);
			}
		}
		return null;
	}

	@Override
	public Clause startCheck() {
		mnumqs = 0;
		mnumqb = 0;
		return null;
	}
	
	@Override
	public void endCheck() {}

	private CCTrigger insert(CCTerm[] initregs, CCTrigger what,
			CCTrigger where, List<CCTrigger> insertionPath) {
		CCTrigger root = where;
		CCTrigger prev = null;
		while (!(what instanceof YieldTrigger)) {
			while (what.equals(where)) {
				prev = where;
				what = what.next();
				where = where.next();
			}
			if (where instanceof GotoTrigger) {
				GotoTrigger gototrig = (GotoTrigger) where;
				CCTrigger tmp = gototrig.add(what);
				insertionPath.add(tmp);
				if (tmp == what) {
					// No compatible instruction found => No further merges
					return root;
				}
				// Trivial assertion: YieldTriggers are incompatible
				assert (!(tmp instanceof YieldTrigger));
				prev = tmp;
				where = tmp.next();
				what = what.next();
			} else {
				CCTrigger tmp = new GotoTrigger(where, what);
				insertionPath.add(what);
				if (prev == null) {
					// Top level goto
					return tmp;
				}
				((NonYieldTrigger) prev).next = tmp;
				// No further merges
				return root;
			}
		}
		// Compatible until the yield instruction...
		CCTrigger tmp = new GotoTrigger(where, what);
		assert (prev != null) : "Strange trigger: only a yield instruction!";
		((NonYieldTrigger) prev).next = tmp;
		insertionPath.add(what);
		return root;
	}

	public void add(TriggerData td) {
//		System.err.println("Adding trigger with weight " + td.weight + " Sequence: " + td);
		CCTerm[] initregs = td.initregs;
		CCTrigger first = td.first;
		// TODO Is this really necessary?
		// Compute the number of live registers in the chain
		first.getExpectedInputRegisterLength();
		CCTrigger known = m_TriggerTrees.get(initregs);
		if (known == null) {
			m_TriggerTrees.put(initregs, first);
			// No goto, so we do not need to specify a path...
//			TriggerExecutionContext tec =
//				mengine.getRoot().successor(initregs, first);
//			first.match(mengine, initregs, null, 0, tec, tec.getCandidates());
		} else {
			CCTrigger what = first;
			CCTrigger where = known;
			List<CCTrigger> insertionPath = new ArrayList<CCTrigger>();
			CCTrigger inserted = insert(initregs, what, where, insertionPath);
			// This was the old tec...
//			TriggerExecutionContext tec = 
//				mengine.getRoot().successor(initregs, known);
			if (inserted != known) {
				assert (inserted instanceof GotoTrigger);
				m_TriggerTrees.put(initregs, inserted);
//				TriggerExecutionContext tmp = tec;
//				// This is the tec we should use from now on
//				tec = mengine.getRoot().successor(initregs, inserted);
//				// Share root successor set
//				tec.addSuccessor(tmp);
			}
			// TODO Should this also be delayed into CClosure.checkpoint?
			// Might be better for reverse triggers since we then have a
			// complete congruence graph.
//			inserted.match(mengine, initregs, insertionPath, 0, tec,
//					tec.getCandidates());
		}
	}

	private void remove(TriggerData td) {
		CCTerm[] initregs = td.initregs;
		CCTrigger first = td.first;
		CCTrigger known = m_TriggerTrees.get(initregs);
		assert(known != null);
		CCTrigger tmp = remove(first, known, td.yieldTrigger);
		if (tmp == null) {
			m_TriggerTrees.remove(initregs);
			/*
			 * XXX This if condition looks strange. Cannot figure out why it is
			 * needed. Need comment on that!
			 */
		} else if (tmp != first) {
			assert (known instanceof GotoTrigger);
			m_TriggerTrees.put(initregs, tmp);
		}
	}

	private CCTrigger remove(CCTrigger what, CCTrigger where,
			YieldTrigger target) {
		CCTrigger initial = where;
		Deque<TriggerPair> parentStack = new ArrayDeque<TriggerPair>();
		while (where != target) {
			parentStack.push(new TriggerPair(where, what));
			if (where instanceof GotoTrigger) {
				where = ((GotoTrigger) where).find(what);
			} else {
				where = where.next();
				what = what.next();
			}
		}
		while (!parentStack.isEmpty()) {
			TriggerPair tp = parentStack.pop();
			if (tp.t1 instanceof GotoTrigger) {
				GotoTrigger gototrig = (GotoTrigger) tp.t1;
				int size = gototrig.remove(tp.t2);
				if (size == 1) {
					if (parentStack.isEmpty()) {
						// Toplevel goto
						return gototrig.getSingleElement();
					} else {
						((NonYieldTrigger) parentStack.pop().t1).next = gototrig
								.getSingleElement();
						return initial;
					}
				}
			}
		}
		// Only trigger for this initial registers
		return null;
	}

	@Override
	public Clause backtrackComplete() {
		// TODO Here we should collect and remove all clauses that stem from instantiations.
		return null;
	}
	
	/**
	 * Returns the old number of skolemizations and increases the number.
	 * @return Current number of skolemizations.
	 */
	public int skolemcounter() {
		return skolemcounter++;
	}
	
	private final static CCTerm[] EMPTY_REGS = {};
	
	public void createArrayAxioms(Clausifier converter,Term sub1,Term sub2,
			FunctionSymbol select,FunctionSymbol store,TermVariable array,
			TermVariable i1,TermVariable i2,TermVariable elem) {
		ArrayInstantiationUnifier aiu =
			new ArrayInstantiationUnifier(array,i1,i2,elem);
		Map<TermVariable,Term> empty = Collections.emptyMap();
		LinkedHashMap<TermVariable,Integer> subst =
			new LinkedHashMap<TermVariable, Integer>(3,1);
		// forall a,i,v select(store(a,i,v),i) == v
		subst.put(array,0);
		subst.put(i1,1);
		subst.put(elem,2);
		YieldTrigger yield = new YieldTrigger(subst);
		yield.postInit(converter, empty, sub1, aiu);
		FindTrigger root = new FindTrigger(mengine,store,new int[]{-1,0,1,2},
				yield);
		TriggerData td = new TriggerData(root,EMPTY_REGS,yield);
		add(td);
		// forall a,i,j,v i!=j ==> select(store(a,i,v),j) == select(a,j)
		//  trigger: select(store(a,i,v),j) 
//		subst = new LinkedHashMap<TermVariable, Integer>(4,1);
//		subst.put(array, 1);
//		subst.put(i1, 2);
//		subst.put(i2, 0);
//		subst.put(elem, 3);
		yield = new ArrayYieldTrigger(array,elem,i1,i2,1,3,2,0);//YieldTrigger(subst);
		yield.postInit(converter,empty,sub2, aiu);
		ReverseTrigger rev = 
			new ReverseTrigger(mengine,select,0,0,new int[]{-1,0},yield);
		root = new FindTrigger(mengine,store,new int[]{0,1,2,3},rev);
		td = new TriggerData(root,EMPTY_REGS,yield);
		add(td);
		//  trigger: store(a,i,v) select(a,j)
//		subst = new LinkedHashMap<TermVariable, Integer>(4,1);
//		subst.put(array, 0);
//		subst.put(i1, 1);
//		subst.put(i2, 3);
//		subst.put(elem, 2);
		yield = new ArrayYieldTrigger(array,elem,i1,i2,0,2,1,3);//YieldTrigger(subst);
		yield.postInit(converter, empty, sub2, aiu);
		rev = new ReverseTrigger(mengine,select,0,0,new int[]{-1,3},yield);
		root = new FindTrigger(mengine,store,new int[]{-1,0,1,2},rev);
		td = new TriggerData(root,EMPTY_REGS,yield);
		add(td);
	}

	@Override
	public void pop(Object object, int unused) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public Object push() {
		return null;
	}

	@Override
	public void removeAtom(DPLLAtom atom) {}

	@Override
	public Object[] getStatistics() {
		return new Object[] {
				":Quant", "Not_Implemented"
		};
	}

	@Override
	public void fillInModel(Model model, Theory t, SharedTermEvaluator ste) {
		// TODO Auto-generated method stub
		
	}
	
}
