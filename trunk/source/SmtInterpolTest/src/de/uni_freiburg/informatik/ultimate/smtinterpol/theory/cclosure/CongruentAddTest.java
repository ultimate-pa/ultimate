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


import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier.CCTermBuilder;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TestCaseWithLogger;

/**
 * Tests the addition of a term congruent to another term and the building
 * of the congruence graph.
 * 
 * Tests:
 * 
 * 1: x0=x1 and f(x0) then add f(x1)
 * 2: x2=x3 then add f(x2) and f(x3)
 * 3: x4=x5 then add g(f(x4)) and g(f(x5))
 * 4: add h(x0,x2,x4) and h(x1,x2,x3)
 * 5: a=b and b=c with terms f(b), and f(c) then create f(a), retract b=c, build congruence, and check f(a)=f(b)
 * @author Juergen Christ
 */
public class CongruentAddTest extends TestCaseWithLogger {
	Theory theory;
	Clausifier clausifier;
	CClosure engine;
	CCTerm[] terms;
	FunctionSymbol f,g,h;
	CCEquality[] equalities;
	CCTerm a,b,c,d;
	CCTerm fa,fb,fc,fd;
	CCEquality ab=null,bc=null,cd=null;
	
	public CongruentAddTest() {
		theory = new Theory(Logics.QF_UF);
		Logger logger = Logger.getRootLogger();
        DPLLEngine dpllEngine = new DPLLEngine(theory, logger);
		clausifier = new Clausifier(dpllEngine, 0);
		clausifier.setLogic(Logics.QF_UF);
		engine = clausifier.getCClosure();
		createterms();
	}
		
	private void createterms() {
		theory.declareSort("U", 0);
		Sort sort = theory.getSort("U");
		Sort[] paramSort = {sort};
		Sort[] paramSort2 = {sort,sort,sort};
		f = theory.declareFunction("f", paramSort, sort);
		g = theory.declareFunction("g", paramSort, sort);
		h = theory.declareFunction("h", paramSort2, sort);
		terms = new CCTerm[6];
		CCTerm[] EMPTY_PARAMS = new CCTerm[0];
		Sort[] EMPTY_SORTS = new Sort[0];
		for (int i = 0; i < 6; ++i) {
			FunctionSymbol sym = theory.declareFunction("x"+i, EMPTY_SORTS, sort);
			terms[i]  = engine.createFuncTerm(sym, EMPTY_PARAMS,null); 
		}
		FunctionSymbol funcd = theory.declareFunction("d", EMPTY_SORTS, sort);
		FunctionSymbol funcc = theory.declareFunction("c", EMPTY_SORTS, sort);
		FunctionSymbol funcb = theory.declareFunction("b", EMPTY_SORTS, sort);
		FunctionSymbol funca = theory.declareFunction("a", EMPTY_SORTS, sort);
		d = engine.createFuncTerm(funcd, EMPTY_PARAMS, null);
		c = engine.createFuncTerm(funcc, EMPTY_PARAMS, null);
		b = engine.createFuncTerm(funcb, EMPTY_PARAMS, null);
		a = engine.createFuncTerm(funca, EMPTY_PARAMS, null);
		SharedTerm shareda = clausifier.getSharedTerm(theory.term(funca));
		SharedTerm sharedb = clausifier.getSharedTerm(theory.term(funcb));
		SharedTerm sharedc = clausifier.getSharedTerm(theory.term(funcc));
		SharedTerm sharedd = clausifier.getSharedTerm(theory.term(funcd));
		CCTermBuilder builder = clausifier.new CCTermBuilder();
		builder.convert(shareda.getTerm());
		builder.convert(sharedb.getTerm());
		builder.convert(sharedc.getTerm());
		builder.convert(sharedd.getTerm());
		EqualityProxy eqab = clausifier.createEqualityProxy(shareda, sharedb);
		assertNotSame(EqualityProxy.getTrueProxy(), eqab);
		assertNotSame(EqualityProxy.getFalseProxy(), eqab);
		EqualityProxy eqbc = clausifier.createEqualityProxy(sharedb, sharedc);
		assertNotSame(EqualityProxy.getTrueProxy(), eqbc);
		assertNotSame(EqualityProxy.getFalseProxy(), eqbc);
		EqualityProxy eqcd = clausifier.createEqualityProxy(sharedc, sharedd);
		assertNotSame(EqualityProxy.getTrueProxy(), eqcd);
		assertNotSame(EqualityProxy.getFalseProxy(), eqcd);
		ab = (CCEquality) eqab.getLiteral();
		bc = (CCEquality) eqbc.getLiteral();
		cd = (CCEquality) eqcd.getLiteral();
		fc = engine.createFuncTerm(f, new CCTerm[]{c}, null);
		fb = engine.createFuncTerm(f, new CCTerm[]{b}, null);
		equalities = new CCEquality[3];
		for (int i = 0; i < 3; ++i)
			equalities[i] = engine.createCCEquality(1, terms[2*i], terms[2*i+1]);
	}
	
	public void testCase1() {
		CCTerm[] sub1 = {terms[0]};
		CCTerm t1 = engine.createFuncTerm(f, sub1, null);
		Clause conflict = terms[0].merge(engine, terms[1], equalities[0]);
		assertNull(conflict);
		CCTerm[] sub2 = {terms[1]};
		CCTerm t2 = engine.createFuncTerm(f, sub2, null);
		conflict = engine.checkpoint();
		assertNull(conflict);
		assertSame(t1.getRepresentative(), t2.getRepresentative());
	}
	
	
	
	
	
	public void testCase2() {
		Clause conflict = terms[2].merge(engine, terms[3], equalities[1]);
		assertNull(conflict);
		CCTerm[] sub1 = {terms[2]};
		CCTerm[] sub2 = {terms[3]};
		CCTerm t1 = engine.createFuncTerm(f, sub1, null);
		CCTerm t2 = engine.createFuncTerm(f, sub2, null);
		conflict = engine.checkpoint();
		assertNull(conflict);
		assertSame(t1.getRepresentative(), t2.getRepresentative());
	}
	
	public void testCase3() {
		Clause conflict = terms[4].merge(engine, terms[5], equalities[2]);
		assertNull(conflict);
		CCTerm[] sub1 = {terms[4]};
		CCTerm[] sub2 = {terms[5]};
		CCTerm[] gsub1 = {engine.createFuncTerm(f, sub1, null)};
		CCTerm[] gsub2 = {engine.createFuncTerm(f, sub2, null)};
		assertNotSame(gsub1[0].getRepresentative(), gsub2[0].getRepresentative());
		CCTerm t1 = engine.createFuncTerm(g, gsub1, null);
		CCTerm t2 = engine.createFuncTerm(g, gsub2, null);
		assertNotSame(t1.getRepresentative(), t2.getRepresentative());
		conflict = engine.checkpoint();
		assertNull(conflict);
		assertSame(t1.getRepresentative(), t2.getRepresentative());
	}
	
	public void testCase4() {
		Clause conflict = terms[0].merge(engine, terms[1], equalities[0]);
		assertNull(conflict);
		conflict = terms[2].merge(engine, terms[3], equalities[1]);
		assertNull(conflict);
		conflict = terms[4].merge(engine, terms[5], equalities[2]);
		assertNull(conflict);
		CCTerm[] args1 = {terms[0],terms[2],terms[4]};
		CCTerm[] args2 = {terms[1],terms[3],terms[5]};
		for (int i = 0; i < 3; ++i)
			assertSame(terms[2*i].getRepresentative(),terms[2*i+1].getRepresentative());
		CCTerm t1 = engine.createFuncTerm(h, args1, null);
		CCTerm t2 = engine.createFuncTerm(h, args2, null);
		conflict = engine.checkpoint();
		assertNull(conflict);
		assertSame(t1.getRepresentative(), t2.getRepresentative());
	}
	
	public void testCase5() {
		Clause conflict = engine.setLiteral(ab);
		assertNull(conflict);
		conflict = engine.setLiteral(cd);
		assertNull(conflict);
		conflict = engine.setLiteral(bc);
		assertNull(conflict);
//		System.err.println("a.repStar = " + a.getRepresentative());
//		System.err.println("b.repStar = " + b.getRepresentative());
//		System.err.println("c.repStar = " + c.getRepresentative());
		// Create congruence closure
		conflict = engine.checkpoint();
		assertNull(conflict);
		long time = System.nanoTime();
		fa = engine.createFuncTerm(f, new CCTerm[]{a}, null);
		time -= System.nanoTime();
		engine.engine.getLogger().info("f(a)-creation time: " + -time);
		// We can even remove this step and still get an error
		conflict = engine.checkpoint();
		assertNull(conflict);
//		System.err.println("fa.repStar = " + fa.getRepresentative());
//		System.err.println("fb.repStar = " + fb.getRepresentative());
//		System.err.println("fc.repStar = " + fc.getRepresentative());
		assertSame(fa.getRepresentative(), fb.getRepresentative());
		assertSame(fb.getRepresentative(), fc.getRepresentative());
		time = System.nanoTime();
		fd = engine.createFuncTerm(f, new CCTerm[]{d}, null);
		time -= System.nanoTime();
		engine.engine.getLogger().info("f(d)-creation time: " + -time);
		conflict = engine.checkpoint();
		assertNull(conflict);
		assertSame(fa.getRepresentative(), fb.getRepresentative());
		assertSame(fb.getRepresentative(), fc.getRepresentative());
		assertSame(fc.getRepresentative(), fd.getRepresentative());
		engine.backtrackLiteral(bc);
		conflict = engine.checkpoint();
		assertNull(conflict);
		assertSame(a.getRepresentative(), b.getRepresentative());
		assertNotSame(b.getRepresentative(), c.getRepresentative());
		assertSame(c.getRepresentative(), d.getRepresentative());
		assertNotSame(fb.getRepresentative(),fc.getRepresentative());
		assertSame(fc.getRepresentative(), fd.getRepresentative());
		assertSame(fa.getRepresentative(), fb.getRepresentative());
	}
}
