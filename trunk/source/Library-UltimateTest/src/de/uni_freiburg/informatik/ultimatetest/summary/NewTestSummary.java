package de.uni_freiburg.informatik.ultimatetest.summary;

import java.io.File;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.util.Util;
import de.uni_freiburg.informatik.ultimatetest.util.Util.IPredicate;
import de.uni_freiburg.informatik.ultimatetest.util.Util.IReduce;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public abstract class NewTestSummary implements ITestSummary {

	protected HashMap<UltimateRunDefinition, ExtendedResult> mResults;
	private Class<? extends UltimateTestSuite> mUltimateTestSuite;

	public NewTestSummary(Class<? extends UltimateTestSuite> ultimateTestSuite) {
		mResults = new HashMap<>();
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

	protected class ExtendedResult {
		public ExtendedResult(TestResult result, String message, String category, String testname) {
			Result = result;
			Message = message;
			Category = category;
			Testname = testname;
		}

		public TestResult Result;
		public String Message;
		public String Category;
		public String Testname;
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

	}

	protected PartitionedResults partitionResults(Collection<Entry<UltimateRunDefinition, ExtendedResult>> all) {
		final LinkedHashSet<Entry<UltimateRunDefinition, ExtendedResult>> goodResults = new LinkedHashSet<>();
		goodResults.addAll(Util.where(all, new ITestSummaryResultPredicate() {
			@Override
			public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getValue().Result == TestResult.SUCCESS;
			}
		}));

		final LinkedHashSet<Entry<UltimateRunDefinition, ExtendedResult>> timeoutResults = new LinkedHashSet<>();
		timeoutResults.addAll(Util.where(all, new ITestSummaryResultPredicate() {
			@Override
			public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return (entry.getValue().Result == TestResult.UNKNOWN && entry.getValue().Message.toLowerCase()
						.contains("timeout"));
			}
		}));
		Collection<Entry<UltimateRunDefinition, ExtendedResult>> errorResults = Util.where(all,
				new ITestSummaryResultPredicate() {
					@Override
					public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
						return !goodResults.contains(entry) && !timeoutResults.contains(entry);
					}
				});

		final LinkedHashSet<Entry<UltimateRunDefinition, ExtendedResult>> unsafeResults = new LinkedHashSet<>();
		unsafeResults.addAll(Util.where(goodResults, new ITestSummaryResultPredicate() {
			@Override
			public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getValue().Message.contains("UNSAFE");
			}
		}));

		Collection<Entry<UltimateRunDefinition, ExtendedResult>> safeResults = Util.where(goodResults,
				new ITestSummaryResultPredicate() {
					@Override
					public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
						return !unsafeResults.contains(entry);
					}
				});
		PartitionedResults rtr = new PartitionedResults();

		int expectedSafe = 0;
		int expectedUnsafe = 0;
		for (Entry<UltimateRunDefinition, ExtendedResult> entry : all) {
			if (entry.getValue().Message.contains("ExpectedResult: UNSAFE")) {
				expectedUnsafe++;
			}
			if (entry.getValue().Message.contains("ExpectedResult: SAFE")) {
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

		rtr.Success = Util.where(all, new ITestSummaryResultPredicate() {
			@Override
			public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getValue().Result == TestResult.SUCCESS;
			}
		});

		rtr.Unknown = Util.where(all, new ITestSummaryResultPredicate() {
			@Override
			public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getValue().Result == TestResult.UNKNOWN;
			}
		});

		rtr.Failure = Util.where(all, new ITestSummaryResultPredicate() {
			@Override
			public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getValue().Result == TestResult.FAIL;
			}
		});

		return rtr;
	}

	protected class PartitionedResults {
		public Collection<Entry<UltimateRunDefinition, ExtendedResult>> All;
		public Collection<Entry<UltimateRunDefinition, ExtendedResult>> Timeout;
		public Collection<Entry<UltimateRunDefinition, ExtendedResult>> Error;
		public Collection<Entry<UltimateRunDefinition, ExtendedResult>> Unsafe;
		public Collection<Entry<UltimateRunDefinition, ExtendedResult>> Safe;
		public Collection<Entry<UltimateRunDefinition, ExtendedResult>> Success;
		public Collection<Entry<UltimateRunDefinition, ExtendedResult>> Unknown;
		public Collection<Entry<UltimateRunDefinition, ExtendedResult>> Failure;
		public int ExpectedSafe;
		public int ExpectedUnsafe;

		private PartitionedResults() {

		}

		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append("Safe: ").append(Safe.size());
			sb.append(Util.getPlatformLineSeparator());
			sb.append("Unsafe: ").append(Unsafe.size());
			sb.append(Util.getPlatformLineSeparator());
			sb.append("Timeout: ").append(Timeout.size());
			sb.append(Util.getPlatformLineSeparator());
			sb.append("Error: ").append(Error.size());
			sb.append(Util.getPlatformLineSeparator());
			sb.append("Expected Safe: ").append(ExpectedSafe);
			sb.append(Util.getPlatformLineSeparator());
			sb.append("Expected Unsafe: ").append(ExpectedUnsafe);
			sb.append(Util.getPlatformLineSeparator());
			sb.append("Total: ").append(All.size());
			return sb.toString();
		}
	}

	protected interface IMyReduce<T> extends IReduce<T, Entry<UltimateRunDefinition, ExtendedResult>> {
	}

	protected interface ITestSummaryResultPredicate extends IPredicate<Entry<UltimateRunDefinition, ExtendedResult>> {
	}

}