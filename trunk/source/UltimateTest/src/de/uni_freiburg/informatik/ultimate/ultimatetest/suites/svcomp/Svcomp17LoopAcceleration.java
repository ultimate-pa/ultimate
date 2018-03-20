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

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompReachTestResultDecider;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class Svcomp17LoopAcceleration extends AbstractSvcompTestSuite {

	@Override
	protected ITestResultDecider getTestResultDecider(final UltimateRunDefinition urd) {
		return new SvcompReachTestResultDecider(urd, false);
	}

	@Override
	protected long getTimeout() {
		// Timeout for each test case in milliseconds
		return 90 * 1000;
	}

	@Override
	protected int getFilesPerCategory() {
		// -1 or value larger than 0
		return -1;
	}

	@Override
	protected List<SvcompTestDefinition> getTestDefinitions() {
		final List<SvcompTestDefinition> rtr = new ArrayList<>();
		// contains 135 examples
		// rtr.addAll(getForAll("ReachSafety-Arrays", true));

		// contains 94 examples
		// rtr.addAll(getForAll("ReachSafety-ControlFlow", true));
		//
		// // contains 1149 examples
		// rtr.addAll(getForAll("ReachSafety-ECA", true));

		// contains 173 examples
		// rtr.addAll(getForAll("ReachSafety-Heap", true));

		// contains 159 examples
		rtr.addAll(getForAll("ReachSafety-Loops", true));
		//
		// // contains 159 examples
		// rtr.addAll(getForAll("ReachSafety-ProductLines", true));
		//
		// // contains 98 examples
		// rtr.addAll(getForAll("ReachSafety-Recursive", true));
		//
		// // contains 273 examples
		// rtr.addAll(getForAll("ReachSafety-Sequentialized", true));
		//
		// // contains 2795 examples
		// rtr.addAll(getForAll("Systems_DeviceDriversLinux64_ReachSafety", false));

		return rtr;
	}

	private List<SvcompTestDefinition> getForAll(final String set, final int limit, final boolean arch32) {
		return getForAll(set, getTimeout(), limit, arch32);
	}

	private List<SvcompTestDefinition> getForAll(final String set, final boolean arch32) {
		return getForAll(set, getTimeout(), getFilesPerCategory(), arch32);
	}

	private List<SvcompTestDefinition> getForAll(final String set, final long timeout, final int limit,
			final boolean arch32) {
		final List<SvcompTestDefinition> rtr = new ArrayList<>();

		// rtr.add(getTestDefinitionFromExamples(set, "AutomizerCInline.xml",
		// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_Woelfing.epf", timeout, limit));
		// rtr.add(getTestDefinitionFromExamples(set, "AutomizerCInlineTransformed.xml",
		// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_Woelfing.epf", timeout, limit));

		// rtr.add(getTestDefinitionFromExamples(set, "AutomizerCInline.xml",
		// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_FastUpr_EE.epf", timeout, limit));
		// rtr.add(getTestDefinitionFromExamples(set, "AutomizerCInlineTransformed.xml",
		// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_FastUpr_EE.epf", timeout, limit));
		// rtr.add(getTestDefinitionFromExamples(set, "AutomizerCInlineTransformed.xml",
		// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_FastUpr_LE.epf", timeout, limit));
		//
		// rtr.add(getTestDefinitionFromExamples(set, "AutomizerCInline.xml",
		// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_FastUpr_noMod_EE.epf", timeout, limit));
		// rtr.add(getTestDefinitionFromExamples(set, "AutomizerCInlineTransformed.xml",
		// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_FastUpr_noMod_EE.epf", timeout, limit));
		// rtr.add(getTestDefinitionFromExamples(set, "AutomizerCInlineTransformed.xml",
		// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_FastUpr_noMod_LE.epf", timeout, limit));

		// rtr.add(getTestDefinitionFromExamples(set, "AutomizerCInline.xml",
		// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_Mohr.epf", timeout, limit));
		// rtr.add(getTestDefinitionFromExamples(set, "AutomizerCInlineTransformed.xml",
		// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_Mohr.epf", timeout, limit));

		rtr.add(getTestDefinitionFromExamples(set, "AutomizerCInline.xml",
				"loopacceleration/svcomp-Reach-32bit-Automizer_Default_Werner.epf", timeout, limit));
		rtr.add(getTestDefinitionFromExamples(set, "AutomizerCInlineTransformed.xml",
				"loopacceleration/svcomp-Reach-32bit-Automizer_Default_Werner.epf", timeout, limit));

		return rtr;
	}
}
