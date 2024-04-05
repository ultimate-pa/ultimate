/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompTestResultDeciderUnreachCall;
import de.uni_freiburg.informatik.ultimate.test.util.SvcompFolderSubset;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author klumpp@informatik.uni-freiburg.de
 *
 */
public class DynamicAbstractionsTestSuite extends AbstractTraceAbstractionTestSuite {

	/** Timeout in seconds. */
	private static final int TIMEOUT = 300;

	/** Limit the number of files per directory. */
	private static final int FILES_PER_DIR_LIMIT = 5;
	private static final int FILE_OFFSET = 0;

	private static final String PROPERTY = TestUtil.SVCOMP_PROP_UNREACHCALL;

	// @formatter:off
	private static final SvcompFolderSubset[] BENCHMARKS = {
		new SvcompFolderSubset("examples/svcomp/pthread/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/pthread-atomic/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/pthread-ext/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/pthread-wmm/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/pthread-lit/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/ldv-races/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/ldv-linux-3.14-races/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/pthread-complex/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/pthread-driver-races/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/pthread-C-DAC/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/pthread-divine/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/pthread-nondet/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/goblint-regression/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/weaver/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/pthread-deagle/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new SvcompFolderSubset("examples/svcomp/pthread-race-challenges/", PROPERTY, null, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
	};

	private static final Pair[] SETTINGS = {
			new Pair<>("gemcutter/DynamicStratifiedAbstractions.epf", null),
			new Pair<>("gemcutter/DynamicStratifiedAbstractions-NumberOfVariables.epf", null)
	};


	private static final String[] TOOLCHAINS = {
		"AutomizerCInline.xml"
	};
	// @formatter:on

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		return new SvcompTestResultDeciderUnreachCall(urd, false);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		final long msPerSecond = 1000;
		return TIMEOUT * msPerSecond;
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final SvcompFolderSubset dfep : BENCHMARKS) {
			for (final String toolchain : TOOLCHAINS) {
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionsFromSvcompYaml(dfep, SETTINGS, toolchain,
						getTimeout()));
			}
		}
		return super.createTestCases();
	}
}
