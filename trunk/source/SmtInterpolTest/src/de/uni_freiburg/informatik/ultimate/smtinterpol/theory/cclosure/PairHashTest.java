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



import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TestCaseWithLogger;

/**
 * Test Class for Pair Hash.
 * 
 * @author Jochen Hoenicke
 */
public final class PairHashTest extends TestCaseWithLogger {
	Theory theory;
	CClosure engine;
	CCTerm[] terms;
	
	public PairHashTest() {
		theory = new Theory(Logics.QF_UF);
		Logger logger = Logger.getRootLogger();
		DPLLEngine dpllEngine = new DPLLEngine(theory, logger);
		engine = new CClosure(dpllEngine,null);
		createtermss();
		logger.setLevel(Level.DEBUG);
	}
	
	public void createtermss() {
		theory.declareSort("U", 0);
		Sort sort = theory.getSort("U");
		terms = new CCTerm[100];
		for (int i = 0; i < 100; i++) {
			FunctionSymbol sym = theory.declareFunction("x"+i, new Sort[0], sort);
			terms[i]  = engine.createFuncTerm(sym, new CCTerm[0],null); 
		}
	}

	public void testAll() {
		engine.createCCEquality(0, terms[5], terms[7]);
		engine.createCCEquality(0, terms[3], terms[7]);
		engine.createCCEquality(0, terms[5], terms[9]);
		engine.createCCEquality(0, terms[2], terms[11]);
		engine.createCCEquality(0, terms[15], terms[53]);
		engine.createCCEquality(0, terms[4], terms[12]);
		engine.createCCEquality(0, terms[5], terms[13]);
		for (int i = 1; i < 100; i+=i) {
			for (int j = 0; j+i < 100; j+= 2*i) {
				terms[j].merge(engine, terms[j+i], engine.createCCEquality(1, terms[j], terms[j+i]));
			}
		}
		engine.createCCEquality(0, terms[15], terms[9]);
		engine.createCCEquality(0, terms[11], terms[32]);
		engine.createCCEquality(0, terms[3], terms[34]);
		engine.createCCEquality(0, terms[2], terms[6]);
		engine.createCCEquality(0, terms[5], terms[12]);
		engine.createCCEquality(0, terms[4], terms[13]);

		for (int i = 64; i >= 1; i /= 2) {
			for (int j = (99/2/i)*2*i; j >= 0; j-= 2*i) {
				if (j+i < 100) {
					CCTerm lhs = terms[j];
					CCTerm rhs = terms[j+i];
					CCTerm tmp = engine.merges.pop();
					if (tmp == lhs) {
						lhs.repStar.invertEqualEdges();
						lhs.undoMerge(engine, rhs);
					} else {
						assert (tmp == rhs);
						rhs.repStar.invertEqualEdges();
						rhs.undoMerge(engine, lhs);
					}
				}
			}
		}
		assertNotNull(engine.pairHash.getInfo(terms[15],terms[9]));
		assertNotNull(engine.pairHash.getInfo(terms[11],terms[32]));
		assertNotNull(engine.pairHash.getInfo(terms[3],terms[34]));
		assertNotNull(engine.pairHash.getInfo(terms[2],terms[6]));
	}
}