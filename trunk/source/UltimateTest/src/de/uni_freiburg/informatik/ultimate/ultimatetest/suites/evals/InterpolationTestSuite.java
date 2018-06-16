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
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public abstract class InterpolationTestSuite extends AbstractEvalTestSuite {

	public static final String[] C = new String[] { ".c" };
	public static final String[] I = new String[] { ".i" };
	public static final String[] ALL = new String[] { ".i", ".c" };

	protected int getFilesPerDirectory() {
		return Integer.MAX_VALUE;
	}

	protected int getFilesPerDirectoryOffset() {
		return 0;
	}

	@Override
	protected long getTimeout() {
		return 120 * 1000;
	}

	@Override
	protected ColumnDefinition[] getColumnDefinitions() {
		// @formatter:off
		return new ColumnDefinition[]{
				new ColumnDefinition(
						"Runtime (ns)", "Avg. runtime",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(
						"Peak memory consumption (bytes)", "Mem{-}ory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
				new ColumnDefinition(
						"Overall iterations", "Iter{-}ations",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"NumberOfCodeBlocks", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"SizeOfPredicatesFP", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"SizeOfPredicatesBP", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"Conjuncts in SSA", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"Conjuncts in UnsatCore", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"ICC %", "ICC",
						ConversionContext.Percent(true,2), Aggregate.Ignore, Aggregate.Average),
			};
		// @formatter:on
	}

	protected abstract List<DirectoryFileEndingsPair> getDirectories();

	protected abstract List<Pair<String, String>> getToolchainSettings();

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		final List<DirectoryFileEndingsPair> dirs = getDirectories();
		final List<Pair<String, String>> tcsettings = getToolchainSettings();
		for (final Pair<String, String> tcsetting : tcsettings) {
			addTestCase(tcsetting.getFirst(), tcsetting.getSecond(),
					dirs.toArray(new DirectoryFileEndingsPair[dirs.size()]));
		}
		return super.createTestCases();
	}

	protected DirectoryFileEndingsPair getPair(final String dir, final String[] endings) {
		return new DirectoryFileEndingsPair(dir, endings, getFilesPerDirectoryOffset(), getFilesPerDirectory());
	}

	// @formatter:off

	public static List<Pair<String, String>> getMemsafetyAutomizer() {
		final List<Pair<String, String>> rtr = new ArrayList<>();

		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Princess-TreeInterpolation-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-SMTInterpol-TreeInterpolation-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-NestedInterpolation-Integer-Kojak.epf"));

		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-CVC4NYU-FP-UC-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Mathsat-FP-UC-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-SMTInterpol-FP-UC-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-FP-UC-LV-Integer-Kojak.epf"));

		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-BP-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-BP-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-BP-UC-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-BP-UC-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-FP-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-FP-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-FP-UC-Integer-Kojak.epf"));

		return rtr;
	}

	public static List<Pair<String, String>> getMemsafetyImpulse() {
		final List<Pair<String, String>> rtr = new ArrayList<>();

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Princess-TreeInterpolation-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-SMTInterpol-TreeInterpolation-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-NestedInterpolation-Integer-Impulse.epf"));

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-CVC4NYU-FP-UC-LV-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Mathsat-FP-UC-LV-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-SMTInterpol-FP-UC-LV-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-FP-UC-LV-Integer-Impulse.epf"));

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-BP-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-BP-LV-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-BP-UC-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-BP-UC-LV-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-FP-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-FP-LV-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-FP-UC-Integer-Impulse.epf"));

		return rtr;
	}

	public static List<Pair<String, String>> getMemsafetyKojak() {
		final List<Pair<String, String>> rtr = new ArrayList<>();

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Princess-TreeInterpolation-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-SMTInterpol-TreeInterpolation-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-NestedInterpolation-Integer-Kojak.epf"));

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-CVC4NYU-FP-UC-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Mathsat-FP-UC-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-SMTInterpol-FP-UC-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-FP-UC-LV-Integer-Kojak.epf"));

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-BP-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-BP-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-BP-UC-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-BP-UC-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-FP-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-FP-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-FP-UC-Integer-Kojak.epf"));

		return rtr;
	}

	public static List<Pair<String, String>> getReachBitvectorAutomizer() {
		final List<Pair<String, String>> rtr = new ArrayList<>();

		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-NestedInterpolation-Bitvector-Kojak.epf"));

		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/bitvector/Reach-32bit-CVC4NYU-FP-UC-LV-Bitvector-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/bitvector/Reach-32bit-Mathsat-FP-UC-LV-Bitvector-Kojak.epf"));
//		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/bitvector/Reach-32bit-SMTInterpol-FP-UC-LV-Bitvector-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-FP-UC-LV-Bitvector-Kojak.epf"));

		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-BP-Bitvector-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-BP-LV-Bitvector-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-BP-UC-Bitvector-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-BP-UC-LV-Bitvector-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-FP-Bitvector-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-FP-LV-Bitvector-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-FP-UC-Bitvector-Kojak.epf"));

		return rtr;
	}

	public static List<Pair<String, String>> getReachBitvectorImpulse() {
		final List<Pair<String, String>> rtr = new ArrayList<>();

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-NestedInterpolation-Bitvector-Impulse.epf"));

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-CVC4NYU-FP-UC-LV-Bitvector-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Mathsat-FP-UC-LV-Bitvector-Impulse.epf"));
//		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-SMTInterpol-FP-UC-LV-Bitvector-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-FP-UC-LV-Bitvector-Impulse.epf"));

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-BP-Bitvector-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-BP-LV-Bitvector-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-BP-UC-Bitvector-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-BP-UC-LV-Bitvector-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-FP-Bitvector-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-FP-LV-Bitvector-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-FP-UC-Bitvector-Impulse.epf"));

		return rtr;
	}

	public static List<Pair<String, String>> getReachBitvectorKojak() {
		final List<Pair<String, String>> rtr = new ArrayList<>();

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-NestedInterpolation-Bitvector-Kojak.epf"));

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-CVC4NYU-FP-UC-LV-Bitvector-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Mathsat-FP-UC-LV-Bitvector-Kojak.epf"));
//		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-SMTInterpol-FP-UC-LV-Bitvector-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-FP-UC-LV-Bitvector-Kojak.epf"));

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-BP-Bitvector-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-BP-LV-Bitvector-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-BP-UC-Bitvector-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-BP-UC-LV-Bitvector-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-FP-Bitvector-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-FP-LV-Bitvector-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/bitvector/Reach-32bit-Z3-FP-UC-Bitvector-Kojak.epf"));

		return rtr;
	}

	public static List<Pair<String, String>> getReachFloatAutomizer() {
		final List<Pair<String, String>> rtr = new ArrayList<>();
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/float/Reach-32bit-Mathsat-FP-UC-LV-Float-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/float/Reach-32bit-Z3-FP-UC-LV-Float-Kojak.epf"));

		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/float/Reach-32bit-Z3-BP-Float-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/float/Reach-32bit-Z3-BP-LV-Float-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/float/Reach-32bit-Z3-BP-UC-Float-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/float/Reach-32bit-Z3-BP-UC-LV-Float-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/float/Reach-32bit-Z3-FP-Float-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/float/Reach-32bit-Z3-FP-LV-Float-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/float/Reach-32bit-Z3-FP-UC-Float-Kojak.epf"));
		return rtr;
	}

	public static List<Pair<String, String>> getReachFloatKojak() {
		final List<Pair<String, String>> rtr = new ArrayList<>();
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/float/Reach-32bit-Mathsat-FP-UC-LV-Float-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/float/Reach-32bit-Z3-FP-UC-LV-Float-Kojak.epf"));

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/float/Reach-32bit-Z3-BP-Float-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/float/Reach-32bit-Z3-BP-LV-Float-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/float/Reach-32bit-Z3-BP-UC-Float-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/float/Reach-32bit-Z3-BP-UC-LV-Float-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/float/Reach-32bit-Z3-FP-Float-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/float/Reach-32bit-Z3-FP-LV-Float-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/float/Reach-32bit-Z3-FP-UC-Float-Kojak.epf"));

		return rtr;
	}

	public static List<Pair<String, String>> getReachIntegerAutomizer() {
		final List<Pair<String, String>> rtr = new ArrayList<>();

		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/Reach-32bit-Princess-TreeInterpolation-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/Reach-32bit-SMTInterpol-TreeInterpolation-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/Reach-32bit-Z3-NestedInterpolation-Integer-Kojak.epf"));

		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/Reach-32bit-CVC4NYU-FP-UC-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/Reach-32bit-Mathsat-FP-UC-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/Reach-32bit-SMTInterpol-FP-UC-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/Reach-32bit-Z3-FP-UC-LV-Integer-Kojak.epf"));

		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/Reach-32bit-Z3-BP-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/Reach-32bit-Z3-BP-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/Reach-32bit-Z3-BP-UC-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/Reach-32bit-Z3-BP-UC-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/Reach-32bit-Z3-FP-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/Reach-32bit-Z3-FP-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("AutomizerCInline.xml", "kojak/interpolation/Reach-32bit-Z3-FP-UC-Integer-Kojak.epf"));

		return rtr;
	}

	public static List<Pair<String, String>> getReachIntegerImpulse() {
		final List<Pair<String, String>> rtr = new ArrayList<>();

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Princess-TreeInterpolation-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-SMTInterpol-TreeInterpolation-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Z3-NestedInterpolation-Integer-Impulse.epf"));

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-CVC4NYU-FP-UC-LV-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Mathsat-FP-UC-LV-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-SMTInterpol-FP-UC-LV-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Z3-FP-UC-LV-Integer-Impulse.epf"));

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Z3-BP-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Z3-BP-LV-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Z3-BP-UC-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Z3-BP-UC-LV-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Z3-FP-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Z3-FP-LV-Integer-Impulse.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Z3-FP-UC-Integer-Impulse.epf"));

		return rtr;
	}

	public static List<Pair<String, String>> getReachIntegerKojak() {
		final List<Pair<String, String>> rtr = new ArrayList<>();

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Princess-TreeInterpolation-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-SMTInterpol-TreeInterpolation-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Z3-NestedInterpolation-Integer-Kojak.epf"));

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-CVC4NYU-FP-UC-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Mathsat-FP-UC-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-SMTInterpol-FP-UC-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Z3-FP-UC-LV-Integer-Kojak.epf"));

		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Z3-BP-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Z3-BP-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Z3-BP-UC-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Z3-BP-UC-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Z3-FP-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Z3-FP-LV-Integer-Kojak.epf"));
		rtr.add(new Pair<>("KojakCBEV2.xml", "kojak/interpolation/Reach-32bit-Z3-FP-UC-Integer-Kojak.epf"));

		return rtr;
	}


	public List<DirectoryFileEndingsPair> getReachSet() {
		final List<DirectoryFileEndingsPair> rtr = new ArrayList<>();
		rtr.add(getPair("examples/svcomp/array-examples/", I));
		rtr.add(getPair("examples/svcomp/reducercommutativity/", I));
		rtr.add(getPair("examples/svcomp/bitvector/", ALL));
		rtr.add(getPair("examples/svcomp/bitvector-regression/", I));
		rtr.add(getPair("examples/svcomp/bitvector-loops/", I));
		rtr.add(getPair("examples/svcomp/heap-manipulation/", I));
		rtr.add(getPair("examples/svcomp/list-properties/", I));
		rtr.add(getPair("examples/svcomp/ldv-regression/", I));
		rtr.add(getPair("examples/svcomp/ddv-machzwd/", I));
		rtr.add(getPair("examples/svcomp/ntdrivers-simplified/", C));
		rtr.add(getPair("examples/svcomp/ssh-simplified/", C));
		rtr.add(getPair("examples/svcomp/locks/", C));
		rtr.add(getPair("examples/svcomp/ntdrivers/", C));
		rtr.add(getPair("examples/svcomp/ssh/", C));
		rtr.add(getPair("examples/svcomp/eca-rers2012/", C));
		rtr.add(getPair("examples/svcomp/loops/", I));
		rtr.add(getPair("examples/svcomp/loop-acceleration/", I));
		rtr.add(getPair("examples/svcomp/loop-invgen/", I));
		rtr.add(getPair("examples/svcomp/loop-lit/", I));
		rtr.add(getPair("examples/svcomp/loop-new/", I));
		rtr.add(getPair("examples/svcomp/loop-industry-pattern/", C));
		rtr.add(getPair("examples/svcomp/recursive/", C));
		rtr.add(getPair("examples/svcomp/recursive-simple/", C));
		rtr.add(getPair("examples/svcomp/product-lines/", C));
		rtr.add(getPair("examples/svcomp/systemc/", C));
		rtr.add(getPair("examples/svcomp/seq-mthreaded/", C));
		rtr.add(getPair("examples/svcomp/seq-pthread/", I));
		rtr.add(getPair("examples/svcomp/ldv-linux-3.0/", I));
		rtr.add(getPair("examples/svcomp/ldv-linux-3.4-simple/", C));
		rtr.add(getPair("examples/svcomp/ldv-linux-3.7.3/", C));
		rtr.add(getPair("examples/svcomp/ldv-commit-tester/", C));
		rtr.add(getPair("examples/svcomp/ldv-consumption/", C));
		rtr.add(getPair("examples/svcomp/ldv-linux-3.12-rc1/", C));
		rtr.add(getPair("examples/svcomp/ldv-linux-3.16-rc1/", C));
		rtr.add(getPair("examples/svcomp/ldv-validator-v0.6/", C));
		rtr.add(getPair("examples/svcomp/ldv-validator-v0.8/", C));
		rtr.add(getPair("examples/svcomp/ldv-linux-4.2-rc1/", C));
		rtr.add(getPair("examples/svcomp/ldv-challenges/", C));
		return rtr;
	}

	public List<DirectoryFileEndingsPair> getFloatSet() {
		final List<DirectoryFileEndingsPair> rtr = new ArrayList<>();
		rtr.add(getPair("examples/svcomp/floats-cdfpl/", I));
		rtr.add(getPair("examples/svcomp/floats-cbmc-regression/", I));
		rtr.add(getPair("examples/svcomp/float-benchs/", C));
		rtr.add(getPair("examples/svcomp/floats-esbmc-regression/", I));
		return rtr;
	}
	public List<DirectoryFileEndingsPair> getMemsafetyDerefSet() {
		final List<DirectoryFileEndingsPair> rtr = new ArrayList<>();
		return rtr;
	}

	public List<DirectoryFileEndingsPair> getMemsafetyDerefFreeMemtrackSet() {
		final List<DirectoryFileEndingsPair> rtr = new ArrayList<>();
		rtr.add(getPair("examples/svcomp/array-memsafety/", I));
		rtr.add(getPair("examples/svcomp/array-examples/", I));
		rtr.add(getPair("examples/svcomp/memsafety/", I) );
		rtr.add(getPair("examples/svcomp/list-ext-properties/", I) );
		rtr.add(getPair("examples/svcomp/memory-alloca/", I) );
		rtr.add(getPair("examples/svcomp/ldv-memsafety/", I) );
		rtr.add(getPair("examples/svcomp/ldv-memsafety-bitfields/", I) );
		return rtr;
	}
	// @formatter:on
}
