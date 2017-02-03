/*
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
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.svcomp;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.NoTimeoutTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class SVCOMPBlockEncodingTestSuite extends AbstractSVCOMPTestSuite {

	@Override
	protected ITestResultDecider getTestResultDecider(UltimateRunDefinition urd) {
		return new NoTimeoutTestResultDecider(urd);
	}

	@Override
	protected long getTimeout() {
		// Timeout for each test case in milliseconds
		return 90 * 1000L;
	}

	@Override
	protected int getFilesPerCategory() {
		// -1 or value larger than 0
		return -1;
	}

	@Override
	protected List<SVCOMPTestDefinition> getTestDefinitions() {
		final Collection<String> allRelevantSets =
				TestUtil.getFilesRegex(getSVCOMPRootDirectory(), new String[] { ".*\\.set" }).stream()
						.map(a -> a.getName().replaceAll("\\.set", "")).filter(a -> !a.endsWith("-validate"))
						.collect(Collectors.toList());
		final List<SVCOMPTestDefinition> rtr = new ArrayList<>();
		for (final String set : allRelevantSets) {
			rtr.addAll(getForAll(set, 1));
		}
		return rtr;
	}

	private List<SVCOMPTestDefinition> getForAll(final String set, final int limit) {
		return getForAll(set, getTimeout(), limit);
	}

	private List<SVCOMPTestDefinition> getForAll(final String set) {
		return getForAll(set, getTimeout(), getFilesPerCategory());
	}

	/**
	 * Get all settings files in examples/settings/svcomp2016 together with PreprocessingC.xml
	 */
	private List<SVCOMPTestDefinition> getForAll(final String set, final long timeout, final int limit) {
		final String svcompSettingsDir = TestUtil.getPathFromTrunk("examples/settings/svcomp2016");
		final Collection<String> settingsFiles = TestUtil
				.getFilesRegex(new File(svcompSettingsDir), new String[] { ".*\\.epf" }).stream()
				.map(a -> a.getAbsolutePath().replaceAll(".*examples.settings.", "")).collect(Collectors.toList());
		final List<SVCOMPTestDefinition> rtr = new ArrayList<>();
		for (final String settingsFile : settingsFiles) {
			rtr.add(getTestDefinitionFromExamples(set, "PreprocessingC.xml", settingsFile, timeout, limit));
			rtr.add(getTestDefinitionFromExamples(set, "PreprocessingCWithBE.xml", settingsFile, timeout, limit));
		}

		return rtr;
	}
}
