/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Test Library.
 * 
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Test Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;

/**
 *  Represents a subset from {@link InliningTest}, which is currently investigated.
 * 
 * 	@author schaetzc@informatik.uni-freiburg.de
 */
public class InliningTest_Individual extends AbstractTraceAbstractionTestSuite {
	
	/** Tests that pass without inlining, but fail with inlining. */
	private static final String[] sFiles = {
		// passes with z3-v4.3.3, fails with z3-v4.4 due to memory
//		"examples/programs/quantifier/regression/c/Aliasing01-Safe.c",
		
		// AssertionError: "Simplification unsound?"
//		"examples/programs/quantifier/regression/ArrowOperator01-read-Safe.c",
//		"examples/programs/quantifier/regression/ArrowOperator03-write-Safe.c",
//		"examples/programs/quantifier/regression/ArrowOperator06-nested-Safe.c",
//		"examples/programs/quantifier/regression/c/SelfReferencingStruct01-Safe.c",
//
//		// Error: "Neither filename nor path nor first line contains a keyword that defines the expected result"
//		// (Error from above, when #Safe or #Unsafe is added)
//		"examples/programs/quantifier/regression/UnconfirmedAliasingProblem2.c",
//		"examples/programs/quantifier/regression/todo/auxVarType.c",
//		"examples/programs/quantifier/regression/copyStructThatIsOnHeap.c",
		
		// Error in BoogiePreprocessor, regarding quantifiers
//		"examples/BoogiePL/schaetzc/TestMultiQuant.bpl",
		
		// Former problem with requires specifications of main procedures.
		"examples/programs/recursive/regression/Katharinenberg.bpl",
		"examples/programs/recursive/regression/Katharinenberg.c",
	};
	
	private static final boolean sTraceAbstractionBoogie = true;
	private static final boolean sTraceAbstractionBoogieInline = true;
	private static final boolean sTraceAbstractionC = true;
	private static final boolean sTraceAbstractionCInline = true;

	@Override
	public long getTimeout() {
		return 12 * 1000;
	}
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final String file : sFiles) {
			if (file.matches(".*\\.bpl$")) {
				if (sTraceAbstractionBoogie) {
					addTestCase(
							"AutomizerBpl.xml",
							"automizer/ForwardPredicates.epf",
						    file);
				}
				if (sTraceAbstractionBoogieInline) {
					addTestCase(
							"AutomizerBplInline.xml",
							"automizer/ForwardPredicates.epf",
						    file);
				}
			} else if (file.matches(".*\\.[ci]$")) {
				if (sTraceAbstractionC) {
					addTestCase(
							"AutomizerC.xml",
							"automizer/ForwardPredicates.epf",
						    file);
				}
				if (sTraceAbstractionCInline) {
					addTestCase(
							"AutomizerCInline.xml",
							"automizer/ForwardPredicates.epf",
						    file);
				}
			}
		}
		return super.createTestCases();
	}

	
}
