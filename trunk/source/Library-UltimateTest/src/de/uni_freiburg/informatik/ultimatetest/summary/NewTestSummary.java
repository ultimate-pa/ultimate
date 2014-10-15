package de.uni_freiburg.informatik.ultimatetest.summary;

import java.io.File;
import java.util.HashMap;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
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

	protected interface IMyReduce<T> extends IReduce<T, Entry<UltimateRunDefinition, ExtendedResult>> {
	}

	protected interface IMyPredicate extends IPredicate<Entry<UltimateRunDefinition, ExtendedResult>> {
	}

}