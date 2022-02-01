/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompReachTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class LdvBugFinding extends AbstractTraceAbstractionTestSuite {

	/** Limit the number of files per directory. */
	private static final int FILES_PER_DIR_LIMIT = Integer.MAX_VALUE;
//	private static final int FILES_PER_DIR_LIMIT = 3;
	private static final int FILE_OFFSET = 0;

	private static final String STANDARD_DOT_C_PATTERN_FALSE = ".*_false-unreach-call.*\\.c";
	private static final String STANDARD_DOT_I_PATTERN_FALSE = ".*_false-unreach-call.*\\.i";

	private static final String BITVECTOR_FOLDER_DOT_C_PATTERN_FALSE = ".*_false-unreach-call.*\\.c";

	// @formatter:off
	private static final DirectoryFileEndingsPair[] BENCHMARKS = {
		
		/***** Category 6. SoftwareSystems *****/
		/*** Subcategory  Systems_DeviceDriversLinux64_ReachSafety ***/
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.0/", new String[]{ STANDARD_DOT_I_PATTERN_FALSE }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.4-simple/", new String[]{ STANDARD_DOT_C_PATTERN_FALSE }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.7.3/", new String[]{ STANDARD_DOT_C_PATTERN_FALSE }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-commit-tester/", new String[]{ STANDARD_DOT_C_PATTERN_FALSE }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-commit-tester/", new String[]{ STANDARD_DOT_C_PATTERN_FALSE }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-consumption/", new String[]{ STANDARD_DOT_C_PATTERN_FALSE }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.12-rc1/", new String[]{ STANDARD_DOT_C_PATTERN_FALSE }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.16-rc1/", new String[]{ STANDARD_DOT_C_PATTERN_FALSE }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-validator-v0.6/", new String[]{ STANDARD_DOT_C_PATTERN_FALSE }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-validator-v0.8/", new String[]{ STANDARD_DOT_C_PATTERN_FALSE }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-4.2-rc1/", new String[]{ STANDARD_DOT_C_PATTERN_FALSE }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-challenges/", new String[]{ STANDARD_DOT_C_PATTERN_FALSE }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.14/", new String[]{ STANDARD_DOT_C_PATTERN_FALSE }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-4.0-rc1-mav/", new String[]{ STANDARD_DOT_C_PATTERN_FALSE }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
		

//		2017-05-07 Matthias: Examples for benchmarks that we only handle with the old (golden) CVC binary		
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-commit-tester/m0_false-unreach-call_drivers-staging-comedi-drivers-ni_660x-ko--107_1a--adbbc36-1.c", new String[]{ STANDARD_DOT_C_PATTERN_FALSE }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-validator-v0.8/linux-stable-af3071a-1-130_7a-drivers--hwmon--s3c-hwmon.ko-entry_point_ldv-val-v0.8_false-unreach-call.cil.out.c", new String[]{ STANDARD_DOT_C_PATTERN_FALSE }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.4-simple/43_1a_cilled_false-unreach-call_ok_linux-43_1a-drivers--usb--gadget--mv_udc.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c", new String[]{ STANDARD_DOT_C_PATTERN_FALSE }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-validator-v0.6/linux-stable-af3071a-1-130_7a-drivers--hwmon--s3c-hwmon.ko-entry_point_false-unreach-call.cil.out.c", new String[]{ STANDARD_DOT_C_PATTERN_FALSE }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.12-rc1/linux-3.12-rc1.tar.xz-144_2a-drivers--input--tablet--gtco.ko-entry_point_false-unreach-call.cil.out.c", new String[]{ STANDARD_DOT_C_PATTERN_FALSE }, FILE_OFFSET, FILES_PER_DIR_LIMIT),
	};
	
	
	
	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		return new SvcompReachTestResultDecider(urd, false);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 120 * 1000;
	}

	/**
	 * List of setting files, path defined relative to the folder
	 * "trunk/examples/settings/",
	 */
	private static final String[] SETTINGS = {
		"automizer/interpolation/bitvector/Reach-32bit-Z3-IcSpLv-Bitvector.epf",
		"automizer/interpolation/bitvector/Reach-32bit-CVC4gold-IcSpLv-Bitvector.epf",
		"automizer/interpolation/bitvector/Reach-32bit-CVC4-IcSpLv-Bitvector.epf",
	};
	

	
	
	private static final String[] TOOLCHAINS = {
		"AutomizerC.xml",
//		"AutomizerCInline.xml",
//		"AutomizerCInlineTransformed.xml",
	};
	// @formatter:on

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final DirectoryFileEndingsPair dfep : BENCHMARKS) {
			for (final String toolchain : TOOLCHAINS) {
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionsFromTrunkRegex(
						new String[] { dfep.getDirectory() }, dfep.getFileEndings(), SETTINGS, toolchain, getTimeout(),
						dfep.getOffset(), dfep.getLimit()));
			}
		}
		return super.createTestCases();
	}

}
