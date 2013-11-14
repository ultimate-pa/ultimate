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
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.PolymorphicFunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.DefaultPatternCompiler;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.TriggerData;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.YieldTrigger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTrigger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CompareTrigger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.FindTrigger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.ReverseTrigger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TestCaseWithLogger;



public class DefaultPatternCompilerTest extends TestCaseWithLogger {

	DefaultPatternCompiler dpc;
	Clausifier clausifier;
	Sort sort;
	Theory theory;
	TermVariable x, y;
	// Functions
	FunctionSymbol f, g, h;
	// Constants
	FunctionSymbol a, b;
	
	Term[] empty;
	
	public DefaultPatternCompilerTest() {
		theory = new Theory(Logics.QF_UFLIRA);
		Logger logger = Logger.getRootLogger();
		DPLLEngine engine = new DPLLEngine(theory, logger);
		clausifier = new Clausifier(engine, 0);
		sort = theory.getSort("Int");
		// FIXME Set to quantifier logic once we support quantifiers.
		clausifier.setLogic(Logics.QF_UFLIRA);
		
		x = theory.createTermVariable("x", sort);
		y = theory.createTermVariable("y", sort);
		
		// Functions
		Sort[] paramTypes = new Sort[3];
		for(int i = 0; i < paramTypes.length; i++)
			paramTypes[i] = sort;
		f = theory.declareFunction("f", paramTypes, sort);
		
		paramTypes = new Sort[1];
		paramTypes[0] = sort;
		g = theory.declareFunction("g", paramTypes, sort);
		
		paramTypes = new Sort[2];
		for(int i = 0; i < paramTypes.length; i++)
			paramTypes[i] = sort;
		h = theory.declareFunction("h", paramTypes, sort);
		
		// Constants
		Sort[] emptySort = new Sort[0];
		a = theory.declareFunction("a", emptySort, sort);
		b = theory.declareFunction("b", emptySort, sort);
		
		dpc = new DefaultPatternCompiler();
		
		empty = new Term[0];
	}
	
	/*
	 * cases:
	 * - 'f(x, y, g(y))'
	 * */
	public void testUnitTrigger() {
		if (true)
			return;
		Term[] triggers = new Term[1];
		Term[] paramC = new Term[1];
		Term[] paramP = new Term[3];
		
		paramC[0] = this.y;
		paramP[0] = this.x;
		paramP[1] = this.y;
		paramP[2] = theory.term(g, paramC);
		triggers[0] = theory.term(f, paramP);
		Set<TermVariable> vars = new HashSet<TermVariable>();
		vars.add(x);
		vars.add(y);
		this.dpc = new DefaultPatternCompiler();
		
		Map<TermVariable, Integer> subst = new HashMap<TermVariable, Integer>();
		subst.put(x, 2);
		subst.put(y, 1);
		YieldTrigger yield = new YieldTrigger(subst);
		CompareTrigger compare = new CompareTrigger(1, 3, yield);
		int reg[] = new int[3];
		reg[0] = -1;
		reg[1] = 2;
		reg[2] = 3;
		ReverseTrigger reverse = new ReverseTrigger(
				clausifier.getCClosure(), f, 2, 0, reg, compare);
		reg = new int[2];
		reg[0] = 0;
		reg[1] = 1;
		FindTrigger find = new FindTrigger(
				clausifier.getCClosure(), g, reg, reverse);
		
		TriggerData expected = new TriggerData(find, null, yield);
		TriggerData actual = this.dpc.compile(vars, triggers, null/*TODO*/);
		assertEquals(expected.toString(), actual.toString());
	}
	
	/*
	 * cases:
	 * - 'g(x), g(y)'
	 */
	public void testMultiTrigger() {
		if (true)
			return;
		Term[] triggers = new Term[2];
		Term[] parameters = new Term[1];
		parameters[0] = x;
		triggers[0] = theory.term(g, parameters);
		parameters = new Term[1];
		parameters[0] = y;
		triggers[1] = theory.term(g, parameters);
		HashSet<TermVariable> vars = new HashSet<TermVariable>();
		vars.add(x);
		vars.add(y);
		
		Map<TermVariable, Integer> subst = new HashMap<TermVariable, Integer>();
		subst.put(x, 0);
		subst.put(y, 1);
		YieldTrigger yield = new YieldTrigger(subst);
		CCTrigger trig1, trig2;
		int[] reg;
		
		reg = new int[2];
		reg[0] = -1;
		reg[1] = 1;
		trig2 = new FindTrigger(clausifier.getCClosure(), g, reg, yield);
		
		reg = new int[2];
		reg[0] = -1;
		reg[1] = 0;
		trig1 = new FindTrigger(clausifier.getCClosure(), g, reg, trig2);
		
		this.dpc = new DefaultPatternCompiler();
		TriggerData expected = new TriggerData(trig1, null, yield);
		TriggerData actual = this.dpc.compile(vars, triggers, null/*TODO*/);
		
		assertEquals(expected.toString(), actual.toString());
	}
	
	/*
	 * Test cases:
	 * - 'x = y'
	 * - 'x = g(x)'
	 * - 'g(x) = x'
	 * - 'g(x) = g(y)'  
	 * */
	public void testClassification() {
		if (true)
			return;
		// Case x = y
		Term[] parameters = new Term[2];
		Term[] triggers	= new Term[1];
		parameters[0] = this.x;
		parameters[1] = this.y;
		PolymorphicFunctionSymbol fseq = theory.m_Equals;
		triggers[0] = theory.term(fseq, parameters);
		Set<TermVariable> vars = new HashSet<TermVariable>();
		vars.add(x);
		vars.add(y);
		this.dpc = new DefaultPatternCompiler();
		
		TriggerData actual = this.dpc.compile(vars, triggers, null /*TODO*/);
		
		assertNull(actual);
		
		// Case x = g(x)
		triggers = new Term[1];
		parameters = new Term[2];
		Term[] parameters2 = new Term[1];
		parameters2[0] = x;
		parameters[0] = x;
		parameters[1] = theory.term(g, parameters2);
		triggers[0] = theory.term(fseq, parameters);
		vars = new HashSet<TermVariable>();
		vars.add(x);
		
		Map<TermVariable, Integer> subst = new HashMap<TermVariable, Integer>();
		subst.put(x, 1);
		YieldTrigger yield = new YieldTrigger(subst);
		
		CCTrigger trig1, trig2;
		int[] reg;
		
		trig2 = new CompareTrigger(0, 1, yield);
		
		reg = new int[2];
		reg[0] = 0;
		reg[1] = 1;
		trig1 = new FindTrigger(clausifier.getCClosure(), g, reg, trig2);
		
		this.dpc = new DefaultPatternCompiler();
		actual = this.dpc.compile(vars, triggers, null/*TODO*/);
		TriggerData expected = new TriggerData(trig1, null, yield);
		
		assertEquals(expected.toString(), actual.toString());
		
		// Case g(x) = x
		parameters[0] = parameters[1];
		parameters[1] = x;
		triggers[0] = theory.term(fseq, parameters);
		
		this.dpc = new DefaultPatternCompiler();
		actual = this.dpc.compile(vars, triggers, null/*TODO*/);
		
		assertEquals(expected.toString(), actual.toString());
		
		// Case g(x) = g(y)
		triggers = new Term[1];
		parameters = new Term[2];
		parameters2 = new Term[1];
		parameters2[0] = x;
		parameters[0] = theory.term(g, parameters2);
		parameters2 = new Term[1];
		parameters[0] = y;
		parameters[1] = theory.term(g, parameters2);
		triggers[0] = theory.term(fseq, parameters);
		
		vars = new HashSet<TermVariable>();
		vars.add(x);
		vars.add(y);
		
		subst = new HashMap<TermVariable, Integer>();
		subst.put(x, 1);
		subst.put(y, 3);
		yield = new YieldTrigger(subst);
		
		trig1 = new CompareTrigger(0, 2, yield);
		
		reg = new int[2];
		reg[0] = 2;
		reg[2] = 3;
		trig2 = new FindTrigger(clausifier.getCClosure(), g, reg, trig1);
		
		reg = new int[2];
		reg[0] = 0;
		reg[1] = 1;
		trig1 = new FindTrigger(clausifier.getCClosure(), g, reg, trig2);
		
		this.dpc = new DefaultPatternCompiler();
		actual = this.dpc.compile(vars, triggers, null/*TODO*/);
		expected = new TriggerData(trig1, null, yield);
		
		assertEquals(expected.toString(), actual.toString());
	}
	
		/*
	 * Test cases:
	 * - 'x = y, g(x)' 
	 */
	public void testPreSorting() {
		if (true)
			return;
		Term[] triggers = new Term[2];;
		Term[] parameters = new Term[2];
		parameters[0] = x;
		parameters[1] = y;
		PolymorphicFunctionSymbol fseq = theory.m_Equals;
		triggers[0] = theory.term(fseq, parameters);
		parameters = new Term[1];
		parameters[0] = x;
		triggers[1] = theory.term(g, parameters);
		
		Set<TermVariable> vars = new HashSet<TermVariable>();
		vars.add(x);
		vars.add(y);
		
		Map<TermVariable, Integer> subst = new HashMap<TermVariable, Integer>();
		subst.put(x, 0);
		subst.put(y, 0);
		YieldTrigger yield = new YieldTrigger(subst);
		int[] reg = new int[2];
		reg[0] = -1;
		reg[1] = 0;
		CCTrigger trig1 = new FindTrigger(
				clausifier.getCClosure(), g, reg, yield);
		
		this.dpc = new DefaultPatternCompiler();
		TriggerData actual = this.dpc.compile(vars, triggers, null/*TODO*/);
		TriggerData expected = new TriggerData(trig1, null, yield);
		
		assertEquals(expected.toString(), actual.toString());
	}
}