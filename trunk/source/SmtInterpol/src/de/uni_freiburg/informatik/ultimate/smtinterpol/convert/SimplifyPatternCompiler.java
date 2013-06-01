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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.PatternCompilerUtils.InsnSequence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.TermDAG.AppTermNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.TermDAG.Edge;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.TermDAG.TermNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.TermDAG.VarNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.BindTrigger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CompareTrigger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.FindTrigger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.IntAllocator;


/**
 * Pattern compiler trying to simulate the matching algorithm used by Simplify.
 * That is, it tries to match top down using find and bind instructions.
 * @author Juergen Christ
 */
public class SimplifyPatternCompiler implements IPatternCompiler {
	
	@Override
	public TriggerData compile(Set<TermVariable> vars, Term[] triggers,
			Clausifier converter) {
		InsnSequence sequence = new InsnSequence();
		Map<TermVariable,Integer> subst = new HashMap<TermVariable, Integer>();
		TermDAG dag = new TermDAG();
		TermNode[] roots = dag.buildDAG(triggers);
		CCTerm[] initregs = dag.getConstants(converter);
		IntAllocator allocator =
			new IntAllocator(initregs.length,Integer.MAX_VALUE);
		for (TermNode tn : roots) {
			createFind(tn,sequence,allocator,subst,converter);
		}
		sequence.append(new YieldTrigger(subst));
		converter.getEngine().getLogger().debug(sequence);
		return sequence.finish(initregs);
	}

	private void createFind(TermNode tn, InsnSequence sequence,
			IntAllocator allocator, Map<TermVariable, Integer> subst, 
			Clausifier converter) {
		HashMap<TermNode, Integer> compares = new HashMap<TermNode, Integer>();
		AppTermNode atn = (AppTermNode)tn;
		FunctionSymbol fs = atn.getSymbol();
		assert(!tn.isInRegister());
		if (fs.isIntern()) {
			// This is an equality...
			// TODO How to support this?
		} else {
			int[] regCtl = new int[fs.getParameterCount() + 1];
			regCtl[0] = -1;
			for (int i = 1; i < regCtl.length; ++i)
				regCtl[i] = allocator.alloc();
			sequence.append(new FindTrigger(converter.getCClosure(),fs,
					regCtl));
			for (int i = 0; i < atn.getChildCount(); ++i) {
				TermNode dest = atn.getChild(i).getTo();
				if (!dest.isInRegister())
					dest.setRegPos(regCtl[i + 1]);
				else
					compares.put(dest,regCtl[i + 1]);
			}
			for (Edge child : atn.getOutgoing()) {
				append(child,sequence,allocator,subst,converter,compares);
			}
		}
	}

	private void append(Edge child, InsnSequence sequence,
			IntAllocator allocator, Map<TermVariable, Integer> subst,
			Clausifier converter, Map<TermNode, Integer> compares) {
		child.mark();
		TermNode dest = child.getTo();
		Integer comp = compares.get(dest);
		if (comp != null) {
			sequence.append(new CompareTrigger(comp,dest.getRegPos()));
			allocator.free(comp);
		} else if (dest instanceof VarNode) {
			VarNode vn = (VarNode)dest;
			subst.put(vn.getVariable(),vn.getRegPos());
		} else {
			AppTermNode atn = (AppTermNode)dest;
			FunctionSymbol fs = atn.getSymbol();
			int[] regCtl = new int[fs.getParameterCount() + 1];
			regCtl[0] = -1;
			for (int i = 1; i < regCtl.length; ++i)
				regCtl[i] = allocator.alloc();
			sequence.append(new BindTrigger(converter.getCClosure(),
					child.getTo().getRegPos(),fs,regCtl));
			for (int i = 0; i < atn.getChildCount(); ++i) {
				TermNode dest2 = atn.getChild(i).getTo();
				if (!dest2.isInRegister())
					dest2.setRegPos(regCtl[i + 1]);
				else
					compares.put(dest2,regCtl[i + 1]);
			}
			for (Edge child2 : atn.getOutgoing()) {
				append(child2,sequence,allocator,subst,converter,compares);
			}
		}
	}

}
