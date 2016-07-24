/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

/**
 * Collects literals of type int or real found in an RCFG. Some widening
 * operators can use these.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 */
public class RCFGArrayIndexCollector extends RCFGEdgeVisitor {

	private final Set<ApplicationTerm> termSet = new HashSet<>();
	private final Map<IProgramVar, Set<PointerExpression>> pointerMap = new HashMap<IProgramVar, Set<PointerExpression>>();
	private final Map<IProgramVar, Set<IProgramVar>> indexToArraysMap = new HashMap<IProgramVar, Set<IProgramVar>>();
	private Map<TermVariable, IProgramVar> termVarToBooVarMap;

	public RCFGArrayIndexCollector(final RCFGNode root) {
		process(root.getOutgoingEdges());
	}

	private <T extends RCFGEdge> void process(final Collection<T> edges) {
		final Deque<RCFGEdge> worklist = new ArrayDeque<RCFGEdge>();
		final Set<RCFGEdge> finished = new HashSet<RCFGEdge>();

		worklist.addAll(edges);
		while (!worklist.isEmpty()) {
			final RCFGEdge current = worklist.removeFirst();
			if (!finished.add(current)) {
				continue;
			}
			visit(current);
			worklist.addAll(current.getTarget().getOutgoingEdges());
		}
	}

	@Override
	protected void visit(CodeBlock c) {
		c.getPrettyPrintedStatements();
		termSet.addAll(new ArrayIndexFinder().findArrayIndex(c.getTransitionFormula().getFormula()));

		final Iterator<ApplicationTerm> termSetIter = termSet.iterator();
		ApplicationTerm term;
		Term[] terms;
		TermVariable[] termVariableArray;
		final Set<PointerExpression> ptrExprSet = new HashSet<PointerExpression>();
		PointerExpression ptrExpr;
		Map<TermVariable, IProgramVar> ptrExprTermMap;

		termVarToBooVarMap = getTermVarToBooVar(c.getTransitionFormula().getInVars());

		while (termSetIter.hasNext()) {
			term = termSetIter.next();
			terms = term.getParameters();

			if (terms.length >= 2) {

				termVariableArray = term.getFreeVars();
				ptrExprTermMap = new HashMap<TermVariable, IProgramVar>();
				final TermVariable[] termVar = terms[1].getFreeVars();
				final IProgramVar pointerMapKey = termVarToBooVarMap.get(termVariableArray[0]);

				for (final TermVariable tv : termVar) {
					final IProgramVar indexTermVar = termVarToBooVarMap.get(tv);
					if (indexTermVar != null) {
						ptrExprTermMap.put(tv, indexTermVar);

						if (!indexToArraysMap.containsKey(indexTermVar)) {
							final Set<IProgramVar> indexToArraySet = new HashSet<IProgramVar>();
							indexToArraySet.add(pointerMapKey);
							indexToArraysMap.put(indexTermVar, indexToArraySet);
						} else {
							indexToArraysMap.get(indexTermVar).add(pointerMapKey);
						}
					}
				}

				if (terms[0].getSort().isArraySort() && pointerMapKey != null) {

					ptrExpr = new PointerExpression(terms[1], ptrExprTermMap);

					ptrExprSet.add(ptrExpr);

					// BoogieVar key =
					// isContainBoogieVarKey(termVarToBooVarMap.get(termVariableArray[0]));
					// if (key != null) {
					// pointerMap.get(key).add(ptrExpr);
					// } else {
					// pointerMap.put(termVarToBooVarMap.get(termVariableArray[0]),
					// ptrExprSet);
					// }

					if (pointerMap.containsKey(pointerMapKey)) {
						pointerMap.get(pointerMapKey).add(ptrExpr);
					} else {
						pointerMap.put(pointerMapKey, ptrExprSet);
					}

				}
			}
		}
	}

//	private BoogieVar isContainBoogieVarKey(BoogieVar boogieVar) {
//
//		for (BoogieVar bv : pointerMap.keySet()) {
//			if (boogieVar.equals(bv)) {
//				return bv;
//			}
//		}
//		return null;
//
//	}

	private Map<TermVariable, IProgramVar> getTermVarToBooVar(Map<IProgramVar, TermVariable> map) {

		final Map<TermVariable, IProgramVar> result = new HashMap<TermVariable, IProgramVar>();

		for (final Entry<IProgramVar, TermVariable> entry : map.entrySet()) {
			result.put(entry.getValue(), entry.getKey());
		}

		return result;
	}

	@Override
	public String toString() {
		return "";
	}
	
	public Map<IProgramVar, Set<PointerExpression>> getPointerMap () {
		return pointerMap;
	}
	
	public Map<IProgramVar, Set<IProgramVar>> getIndexToArraysMap () {
		return indexToArraysMap;
	}

}