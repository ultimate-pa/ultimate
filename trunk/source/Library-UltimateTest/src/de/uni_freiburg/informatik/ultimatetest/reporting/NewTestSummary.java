/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE UnitTest Library.
 * 
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE UnitTest Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimatetest.reporting;

import java.io.File;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.services.model.IResultService;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public abstract class NewTestSummary implements ITestSummary {

	protected LinkedHashMap<UltimateRunDefinition, ExtendedResult> mResults;
	private Class<? extends UltimateTestSuite> mUltimateTestSuite;

	public NewTestSummary(Class<? extends UltimateTestSuite> ultimateTestSuite) {
		mResults = new LinkedHashMap<>();
		mUltimateTestSuite = ultimateTestSuite;
	}

	@Override
	public Class<? extends UltimateTestSuite> getUltimateTestSuiteClass() {
		return mUltimateTestSuite;
	}

	@Override
	public String getDescriptiveLogName() {
		return this.getClass().getSimpleName();
	}

	@Override
	public String getFilenameExtension() {
		return ".log";
	}

	@Override
	public void addResult(UltimateRunDefinition ultimateRunDefinition, TestResult threeValuedResult, String category,
			String message, String testname, IResultService resultService) {
		mResults.put(ultimateRunDefinition, new ExtendedResult(threeValuedResult, message, category, testname));
	}

	protected class TCS {
		public File Toolchain;
		public File Setting;

		public TCS(File toolchain, File setting) {
			Toolchain = toolchain;
			Setting = setting;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + getOuterType().hashCode();
			result = prime * result + ((Setting == null) ? 0 : Setting.hashCode());
			result = prime * result + ((Toolchain == null) ? 0 : Toolchain.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			TCS other = (TCS) obj;
			if (!getOuterType().equals(other.getOuterType()))
				return false;
			if (Setting == null) {
				if (other.Setting != null)
					return false;
			} else if (!Setting.equals(other.Setting))
				return false;
			if (Toolchain == null) {
				if (other.Toolchain != null)
					return false;
			} else if (!Toolchain.equals(other.Toolchain))
				return false;
			return true;
		}

		private NewTestSummary getOuterType() {
			return NewTestSummary.this;
		}

		@Override
		public String toString() {
			return "Toolchain" + Toolchain + ", Setting" + Setting;
		}
		


	}

	protected PartitionedResults getAllResultsPartitioned() {
		return partitionResults(mResults.entrySet());
	}

	protected PartitionedResults partitionResults(Collection<Entry<UltimateRunDefinition, ExtendedResult>> all) {
		final LinkedHashSet<Entry<UltimateRunDefinition, ExtendedResult>> goodResults = new LinkedHashSet<>();
		goodResults.addAll(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.where(all,
				new ITestSummaryResultPredicate() {
					@Override
					public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
						return entry.getValue().getResult() == TestResult.SUCCESS;
					}
				}));

		final LinkedHashSet<Entry<UltimateRunDefinition, ExtendedResult>> timeoutResults = new LinkedHashSet<>();
		timeoutResults.addAll(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.where(all,
				new ITestSummaryResultPredicate() {
					@Override
					public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
						return (entry.getValue().getResult() == TestResult.UNKNOWN && entry.getValue().getMessage().toLowerCase()
								.contains("timeout"));
					}
				}));
		Collection<Entry<UltimateRunDefinition, ExtendedResult>> errorResults = de.uni_freiburg.informatik.ultimate.core.util.CoreUtil
				.where(all, new ITestSummaryResultPredicate() {
					@Override
					public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
						return !goodResults.contains(entry) && !timeoutResults.contains(entry);
					}
				});

		final LinkedHashSet<Entry<UltimateRunDefinition, ExtendedResult>> unsafeResults = new LinkedHashSet<>();
		unsafeResults.addAll(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.where(goodResults,
				new ITestSummaryResultPredicate() {
					@Override
					public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
						return entry.getValue().getMessage().contains("UNSAFE");
					}
				}));

		Collection<Entry<UltimateRunDefinition, ExtendedResult>> safeResults = de.uni_freiburg.informatik.ultimate.core.util.CoreUtil
				.where(goodResults, new ITestSummaryResultPredicate() {
					@Override
					public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
						return !unsafeResults.contains(entry);
					}
				});
		PartitionedResults rtr = new PartitionedResults();

		int expectedSafe = 0;
		int expectedUnsafe = 0;
		for (Entry<UltimateRunDefinition, ExtendedResult> entry : all) {
			if (entry.getValue().getMessage().contains("ExpectedResult: UNSAFE")) {
				expectedUnsafe++;
			}
			if (entry.getValue().getMessage().contains("ExpectedResult: SAFE")) {
				expectedSafe++;
			}
		}

		rtr.All = all;
		rtr.Timeout = timeoutResults;
		rtr.Error = errorResults;
		rtr.Unsafe = unsafeResults;
		rtr.Safe = safeResults;
		rtr.ExpectedSafe = expectedSafe;
		rtr.ExpectedUnsafe = expectedUnsafe;

		rtr.Success = de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.where(all,
				new ITestSummaryResultPredicate() {
					@Override
					public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
						return entry.getValue().getResult() == TestResult.SUCCESS;
					}
				});

		rtr.Unknown = de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.where(all,
				new ITestSummaryResultPredicate() {
					@Override
					public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
						return entry.getValue().getResult() == TestResult.UNKNOWN;
					}
				});

		rtr.Failure = de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.where(all,
				new ITestSummaryResultPredicate() {
					@Override
					public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
						return entry.getValue().getResult() == TestResult.FAIL;
					}
				});

		return rtr;
	}

	protected class PartitionedResults {
		/**
		 * All results (unpartitioned)
		 */
		public Collection<Entry<UltimateRunDefinition, ExtendedResult>> All;

		/**
		 * Subset of partition "All" where Result is UNKNOWN and result message
		 * contains "timeout" in any casing
		 */
		public Collection<Entry<UltimateRunDefinition, ExtendedResult>> Timeout;

		/**
		 * Results where Result is not SUCCESS and which are not in partition
		 * "Timeout".
		 */
		public Collection<Entry<UltimateRunDefinition, ExtendedResult>> Error;

		/**
		 * Subset of partition "Success" where result message contains the
		 * string "UNSAFE"
		 */
		public Collection<Entry<UltimateRunDefinition, ExtendedResult>> Unsafe;
	
		/**
		 * Subset of partition "Success" where result message contains the
		 * string "SAFE"
		 */
		public Collection<Entry<UltimateRunDefinition, ExtendedResult>> Safe;
		
		/**
		 * Results where Result is SUCCESS
		 */
		public Collection<Entry<UltimateRunDefinition, ExtendedResult>> Success;
		
		/**
		 * Results where Result is UNKNOWN
		 */
		public Collection<Entry<UltimateRunDefinition, ExtendedResult>> Unknown;
		
		/**
		 * Results where Result is FAILURE
		 */
		public Collection<Entry<UltimateRunDefinition, ExtendedResult>> Failure;
		public int ExpectedSafe;
		public int ExpectedUnsafe;

		private PartitionedResults() {

		}

		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append("Safe: ").append(Safe.size());
			sb.append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());
			sb.append("Unsafe: ").append(Unsafe.size());
			sb.append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());
			sb.append("Timeout: ").append(Timeout.size());
			sb.append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());
			sb.append("Error: ").append(Error.size());
			sb.append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());
			sb.append("Expected Safe: ").append(ExpectedSafe);
			sb.append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());
			sb.append("Expected Unsafe: ").append(ExpectedUnsafe);
			sb.append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());
			sb.append("Total: ").append(All.size());
			return sb.toString();
		}
	}

	protected interface IMyReduce<T>
			extends
			de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.IReduce<T, Entry<UltimateRunDefinition, ExtendedResult>> {
	}

	protected interface ITestSummaryResultPredicate
			extends
			de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.IPredicate<Entry<UltimateRunDefinition, ExtendedResult>> {
	}

}
