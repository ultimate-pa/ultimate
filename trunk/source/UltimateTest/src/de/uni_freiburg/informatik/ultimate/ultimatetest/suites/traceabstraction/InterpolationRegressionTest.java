/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class InterpolationRegressionTest extends AbstractTraceAbstractionTestSuite {
	
	
	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		return new SafetyCheckTestResultDecider(urd, true);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 10 * 1000;
	}

	
	private static final String[] ULTIMATE_REPOSITORY_BENCHMARKS = {
//			"examples/programs/regression",
			"examples/programs/quantifier/regression",
//			"examples/programs/quantifier/Arrays",
//			"examples/programs/recursive/regression",
//			"examples/programs/toy",
		};
	
	private static final String[] ULTIMATE_REPOSITORY_INTEGER_SETTINGS = {
			"automizer/interpolationRegression/SpLv-LoopFreeBlock-AlsoCheckMemoryLeak.epf",
			"automizer/interpolationRegression/IcSpLv-LoopFreeBlock-AlsoCheckMemoryLeak.epf",
			"automizer/interpolationRegression/SpLv-SingleStatement-AlsoCheckMemoryLeak.epf",
			"automizer/interpolationRegression/WpLv-LoopFreeBlock-AlsoCheckMemoryLeak.epf",
			"automizer/interpolationRegression/IcWpLv-LoopFreeBlock-AlsoCheckMemoryLeak.epf",
			"automizer/interpolationRegression/WpLv-SingleStatement-AlsoCheckMemoryLeak.epf",
	};
	
	private static final String[] ULTIMATE_REPOSITORY_BITVECTOR_SETTINGS = {
//			"automizer/interpolationRegression/SpLv-LoopFreeBlock-Bitvector-AlsoCheckMemoryLeak.epf",
//			"automizer/interpolationRegression/IcSpLv-LoopFreeBlock-Bitvector-AlsoCheckMemoryLeak.epf",
//			"automizer/interpolationRegression/SpLv-SingleStatement-Bitvector-AlsoCheckMemoryLeak.epf",
//			"automizer/interpolationRegression/WpLv-LoopFreeBlock-Bitvector-AlsoCheckMemoryLeak.epf",
//			"automizer/interpolationRegression/IcWpLv-LoopFreeBlock-Bitvector-AlsoCheckMemoryLeak.epf",
//			"automizer/interpolationRegression/WpLv-SingleStatement-Bitvector-AlsoCheckMemoryLeak.epf", 
	};

	

	private static final String[] BOOGIE_TOOLCHAINS = { 
			"AutomizerBpl.xml",
			"AutomizerBplInline.xml",
	};

	private static final String[] C_TOOLCHAINS = { 
			"AutomizerC.xml",
			"AutomizerCInline.xml",
	};
	// @formatter:on

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final String toolchain : BOOGIE_TOOLCHAINS) {
			for (final String setting : ULTIMATE_REPOSITORY_INTEGER_SETTINGS) {
				addTestCase(toolchain, setting, ULTIMATE_REPOSITORY_BENCHMARKS, new String[] { ".bpl" });
			}
		}
		for (final String toolchain : C_TOOLCHAINS) {
			for (final String setting : ULTIMATE_REPOSITORY_INTEGER_SETTINGS) {
				addTestCase(toolchain, setting, ULTIMATE_REPOSITORY_BENCHMARKS, new String[] { ".c", ".i" });
			}
			for (final String setting : ULTIMATE_REPOSITORY_BITVECTOR_SETTINGS) {
				addTestCase(toolchain, setting, ULTIMATE_REPOSITORY_BENCHMARKS, new String[] { ".c", ".i" });
			}
		}
		return super.createTestCases();
	}

}
