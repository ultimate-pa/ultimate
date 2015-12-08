package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.preferences;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.AIActivator;

/**
 * Container class for the preferences
 * 
 * @author GROSS-JAN
 *
 */
public class AIPreferences {
	// ULTIMATE.start
	private static final String mUltimateStartProcName = "ULTIMATE.start";

	private String mMainMethodNames;
	private int mIterationsUntilWidening;
	private int mIterationsUntilRecursiveWidening;
	private int mParallelStatesUntilMerge;
	private boolean mPostponeWidening;
	private String mWideningFixedNumbers;
	private boolean mWideningAutoNumbers;
	private Set<String> mNumbersForWidening;

	private boolean mGenerateStateAnnotations;
	private boolean mStateChangeLogConsole;
	private boolean mStateChangeLogFile;
	private boolean mStateChangeLogUseSourcePath;
	private String mStateChangeLogPath;

	private boolean mStopAfterAnyError;
	private boolean mStopAfterAllErrors;

	private String mDomainID;
	private String mWideningOpName;
	private String mMergeOpName;

	/* Preferences for the value domain */
	private String mIntValueFactoryID;
	private String mIntWideningOpName;
	private String mIntMergeOpName;

	private String mRealValueFactoryID;
	private String mRealWideningOpName;
	private String mRealMergeOpName;

	private String mBoolValueFactoryID;
	private String mBoolWideningOpName;
	private String mBoolMergeOpName;

	private String mBitVectorValueFactoryID;
	private String mBitVectorWideningOpName;
	private String mBitVectorMergeOpName;

	private String mStringValueFactoryID;
	private String mStringWideningOpName;
	private String mStringMergeOpName;

	/* *********************************
	 * Getter functions
	 */

	public String getMainMethodNames() {
		return mMainMethodNames;
	}

	public int getIterationsUntilWidening() {
		return mIterationsUntilWidening;
	}

	public int getIterationsUntilRecursiveWidening() {
		return mIterationsUntilRecursiveWidening;
	}

	public int getParallelStatesUntilMerge() {
		return mParallelStatesUntilMerge;
	}

	public boolean getPostponeWidening() {
		return mPostponeWidening;
	}

	public String getWideningFixedNumbers() {
		return mWideningFixedNumbers;
	}

	public boolean getWideningAutoNumbers() {
		return mWideningAutoNumbers;
	}

	public Set<String> getNumbersForWidening() {
		return mNumbersForWidening;
	}

	public boolean getGenerateStateAnnotations() {
		return mGenerateStateAnnotations;
	}

	public boolean getStateChangeLogConsole() {
		return mStateChangeLogConsole;
	}

	public boolean getStateChangeLogFile() {
		return mStateChangeLogFile;
	}

	public boolean getStateChangeLogUseSourcePath() {
		return mStateChangeLogUseSourcePath;
	}

	public String getStateChangeLogPath() {
		return mStateChangeLogPath;
	}

	public boolean getStopAfterAnyError() {
		return mStopAfterAnyError;
	}

	public boolean getStopAfterAllErrors() {
		return mStopAfterAllErrors;
	}

	public String getDomainID() {
		return mDomainID;
	}

	public String getWideningOpName() {
		return mWideningOpName;
	}

	public String getMergeOpName() {
		return mMergeOpName;
	}

	/* Preferences for the value domain */
	public String getIntFactoryID() {
		return mIntValueFactoryID;
	}

	public String getIntWideningOpName() {
		return mIntWideningOpName;
	}

	public String getIntMergeOpName() {
		return mIntMergeOpName;
	}

	public String getRealFactoryID() {
		return mRealValueFactoryID;
	}

	public String getRealWideningOpName() {
		return mRealWideningOpName;
	}

	public String getRealMergeOpName() {
		return mRealMergeOpName;
	}

	public String getBoolFactoryID() {
		return mBoolValueFactoryID;
	}

	public String getBoolWideningOpName() {
		return mBoolWideningOpName;
	}

	public String getBoolMergeOpName() {
		return mBoolMergeOpName;
	}

	public String getBitVectorFactoryID() {
		return mBitVectorValueFactoryID;
	}

	public String getBitVectorWideningOpName() {
		return mBitVectorWideningOpName;
	}

	public String getBitVectorMergeOpName() {
		return mBitVectorMergeOpName;
	}

	public String getStringFactoryID() {
		return mStringValueFactoryID;
	}

	public String getStringWideningOpName() {
		return mStringWideningOpName;
	}

	public String getStringMergeOpName() {
		return mStringMergeOpName;
	}

	public String getUltimateStartProcName() {
		return mUltimateStartProcName;
	}

	/**
	 * Get preferences from the preference store
	 */
	public void fetchPreferences() {
		UltimatePreferenceStore prefs = new UltimatePreferenceStore(
				AIActivator.PLUGIN_ID);

		mMainMethodNames = prefs
				.getString(AbstractInterpretationPreferenceInitializer.LABEL_MAIN_METHOD_NAMES);

		mIterationsUntilWidening = prefs
				.getInt(AbstractInterpretationPreferenceInitializer.LABEL_ITERATIONS_UNTIL_WIDENING);
		mIterationsUntilRecursiveWidening = prefs
				.getInt(AbstractInterpretationPreferenceInitializer.LABEL_ITERATIONS_UNTIL_REC_WIDENING);
		mParallelStatesUntilMerge = prefs
				.getInt(AbstractInterpretationPreferenceInitializer.LABEL_STATES_UNTIL_MERGE);
		mPostponeWidening = prefs
				.getBoolean(AbstractInterpretationPreferenceInitializer.LABEL_POSTPONE_WIDENING);

		mWideningFixedNumbers = prefs
				.getString(AbstractInterpretationPreferenceInitializer.LABEL_WIDENING_FIXEDNUMBERS);
		mWideningAutoNumbers = prefs
				.getBoolean(AbstractInterpretationPreferenceInitializer.LABEL_WIDENING_AUTONUMBERS);

		mGenerateStateAnnotations = prefs
				.getBoolean(AbstractInterpretationPreferenceInitializer.LABEL_STATE_ANNOTATIONS);
		mStateChangeLogConsole = prefs
				.getBoolean(AbstractInterpretationPreferenceInitializer.LABEL_LOGSTATES_CONSOLE);
		mStateChangeLogFile = prefs
				.getBoolean(AbstractInterpretationPreferenceInitializer.LABEL_LOGSTATES_FILE);
		mStateChangeLogUseSourcePath = prefs
				.getBoolean(AbstractInterpretationPreferenceInitializer.LABEL_LOGSTATES_USESOURCEPATH);
		mStateChangeLogPath = prefs
				.getString(AbstractInterpretationPreferenceInitializer.LABEL_LOGSTATES_PATH);

		String stopAfter = prefs
				.getString(AbstractInterpretationPreferenceInitializer.LABEL_STOPAFTER);
		mStopAfterAnyError = (stopAfter
				.equals(AbstractInterpretationPreferenceInitializer.OPTION_STOPAFTER_ANYERROR));
		mStopAfterAllErrors = (stopAfter
				.equals(AbstractInterpretationPreferenceInitializer.OPTION_STOPAFTER_ALLERRORS));

		// get domain and operators
		mDomainID = prefs
				.getString(AbstractInterpretationPreferenceInitializer.LABEL_DOMAIN);
		mWideningOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_WIDENINGOP,
				mDomainID));
		mMergeOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_MERGEOP,
				mDomainID));

		// get factories and operators
		mIntValueFactoryID = prefs
				.getString(AbstractInterpretationPreferenceInitializer.LABEL_INTFACTORY);
		mIntWideningOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_WIDENINGOP,
				mIntValueFactoryID));
		mIntMergeOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_MERGEOP,
				mIntValueFactoryID));

		mRealValueFactoryID = prefs
				.getString(AbstractInterpretationPreferenceInitializer.LABEL_REALFACTORY);
		mRealWideningOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_WIDENINGOP,
				mRealValueFactoryID));
		mRealMergeOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_MERGEOP,
				mRealValueFactoryID));

		mBoolValueFactoryID = prefs
				.getString(AbstractInterpretationPreferenceInitializer.LABEL_BOOLFACTORY);
		mBoolWideningOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_WIDENINGOP,
				mBoolValueFactoryID));
		mBoolMergeOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_MERGEOP,
				mBoolValueFactoryID));

		mBitVectorValueFactoryID = prefs
				.getString(AbstractInterpretationPreferenceInitializer.LABEL_BITVECTORFACTORY);
		mBitVectorWideningOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_WIDENINGOP,
				mBitVectorValueFactoryID));
		mBitVectorMergeOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_MERGEOP,
				mBitVectorValueFactoryID));

		mStringValueFactoryID = prefs
				.getString(AbstractInterpretationPreferenceInitializer.LABEL_STRINGFACTORY);
		mStringWideningOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_WIDENINGOP,
				mStringValueFactoryID));
		mStringMergeOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_MERGEOP,
				mStringValueFactoryID));

		mNumbersForWidening = new HashSet<String>();
		if (!mWideningFixedNumbers.isEmpty()) {
			String[] nums = mWideningFixedNumbers.split(",");
			for (int i = 0; i < nums.length; i++) {
				mNumbersForWidening.add(nums[i].trim());
			}
		}
	}
}
