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
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.evals;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompReachTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class InterpolationTestSuiteBitvector extends InterpolationTestSuite {
	
	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
		return new SvcompReachTestResultDecider(ultimateRunDefinition, false);
	}
	
	@Override
	protected List<DirectoryFileEndingsPair> getDirectories() {
		final List<DirectoryFileEndingsPair> rtr = new ArrayList<>();
		rtr.addAll(getReachSet());
		return rtr;
	}
	
	@Override
	protected List<Pair<String, String>> getToolchainSettings() {
		final List<Pair<String, String>> rtr = new ArrayList<>();
		rtr.addAll(getReachBitvectorAutomizer());
		rtr.addAll(getReachBitvectorKojak());
		return rtr;
	}
	
	@Override
	protected int getFilesPerDirectory() {
		// 5 is 4512
		return 5;
	}
	
	@Override
	protected int getFilesPerDirectoryOffset() {
		return 0;
	}
}
