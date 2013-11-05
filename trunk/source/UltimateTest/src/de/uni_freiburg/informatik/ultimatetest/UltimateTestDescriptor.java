package de.uni_freiburg.informatik.ultimatetest;

import java.io.File;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Collection;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logging.UltimateLoggerFactory;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.NoResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;

public class UltimateTestDescriptor {

	protected File mPathSettings;
	protected File mPathToolchain;
	protected File mPathInputFileDirectory;
	protected String[] mFileEndings;
	protected int mDeadline;
	protected TestSummary mSummary;
	protected String mDescription;

	public UltimateTestDescriptor(String pathSettings, String pathToolchain,
			String pathInputFileDirectory, String[] fileEndings, int deadline,
			String description) {
		this(new File(pathSettings), new File(pathToolchain), new File(
				pathInputFileDirectory), fileEndings, deadline,
				new TestSummary(), description);
	}

	protected UltimateTestDescriptor(File pathSettings, File pathToolchain,
			File pathInputFileDirectory, String[] fileEnding, int deadline,
			TestSummary summary, String description) {
		this.mPathSettings = pathSettings;
		this.mPathToolchain = pathToolchain;
		this.mPathInputFileDirectory = pathInputFileDirectory;
		this.mFileEndings = fileEnding;
		this.mDeadline = deadline;
		mSummary = summary;
		mDescription = description;
	}

	public UltimateTestDescriptor copy() {
		return new UltimateTestDescriptor(mPathSettings, mPathToolchain,
				mPathInputFileDirectory, mFileEndings, mDeadline, mSummary,
				mDescription);
	}

	public UltimateTestDescriptor copy(String pathToFile) {
		return new UltimateTestDescriptor(mPathSettings, mPathToolchain,
				new File(pathToFile), mFileEndings, mDeadline, mSummary,
				mDescription);
	}

	public String generateLogFilename() {

		DateFormat dateFormat = new SimpleDateFormat("yyyy-MM-dd-HH-mm-ss");

		String dir = getPathInputFile().getParent() + File.separator;

		String originalFileName = getPathInputFile().getName();
		for (String ending : getFileEndings()) {
			originalFileName = originalFileName.replaceAll(ending, "");
		}

		String name = "UltimateTest " + mDescription + " " + originalFileName
				+ dateFormat.format(Calendar.getInstance().getTime()) + ".log";
		name = name.replaceAll(" ", "_");
		return dir + name;
	}

	public static String generateSummaryLogFilename(String directory,
			String description) {
		DateFormat dateFormat = new SimpleDateFormat("yyyy-MM-dd-HH-mm-ss-SSS");

		if (description == null) {
			description = "";
		}

		if (description.length() > 0) {
			description = description + " ";
		}

		File f = new File(directory);

		String dir = "";
		if (f.isDirectory()) {
			dir = f + File.separator;
		} else {
			dir = f.getParent() + File.separator;
		}
		String name = "UltimateTest Summary " + description
				+ dateFormat.format(Calendar.getInstance().getTime()) + ".log";

		return dir + name;
	}

	public boolean testFailed() {
		Logger log = UltimateLoggerFactory.getInstance().getLoggerById(
				"UltimateTest");
		log.debug("========== TEST RESULTS ==========");
		log.debug("Results for " + getPathInputFile());
		boolean fail = isResultFail(UltimateServices.getInstance()
				.getResultMap().entrySet());
		for (Entry<String, List<IResult>> entry : UltimateServices
				.getInstance().getResultMap().entrySet()) {
			int i = 0;
			for (IResult result : entry.getValue()) {
				log.debug("[" + i + "] " + entry.getKey() + " --> ["
						+ result.getClass().getSimpleName() + "] "
						+ result.getLongDescription());
				++i;
			}
		}

		if (fail) {
			log.debug("TEST FAILED");
		} else {
			log.debug("TEST SUCCEEDED");
		}
		log.debug("============== END ==============");
		return fail;
	}

	public boolean isResultFail(Set<Entry<String, List<IResult>>> resultMap) {
		Set<Entry<String, List<IResult>>> entries = UltimateServices
				.getInstance().getResultMap().entrySet();
		if (entries.isEmpty()) {
			return true;
		}
		for (Entry<String, List<IResult>> entry : entries) {
			for (IResult result : entry.getValue()) {

				if (result instanceof SyntaxErrorResult
						|| result instanceof TimeoutResult
						|| result instanceof NoResult) {
					return true;
				}

			}
		}
		return false;
	}

	public Collection<File> getFiles() {
		return getFiles(mPathInputFileDirectory, mFileEndings);
	}

	protected static Collection<File> getFiles(File root, String[] endings) {

		ArrayList<File> rtr = new ArrayList<File>();

		if (root.isFile()) {
			rtr.add(root);
			return rtr;
		}

		File[] list = root.listFiles();

		if (list == null) {
			return rtr;
		}

		for (File f : list) {
			if (f.isDirectory()) {
				rtr.addAll(getFiles(f, endings));
			} else {

				if (endings == null || endings.length == 0) {
					rtr.add(f);
				} else {
					for (String s : endings) {
						if (f.getAbsolutePath().endsWith(s)) {
							rtr.add(f);
							break;
						}

					}
				}
			}
		}
		return rtr;
	}

	/**
	 * Returns recursively all files in a directory that have a path which is
	 * matched by regex. If root is a file, a collection containing root is
	 * returned (ignoring the regex)
	 * 
	 * @param root
	 * @param regex
	 * @return
	 */
	public static Collection<File> getFilesRegex(File root, String[] regex) {

		ArrayList<File> rtr = new ArrayList<File>();

		if (root.isFile()) {
			rtr.add(root);
			return rtr;
		}

		File[] list = root.listFiles();

		if (list == null) {
			return rtr;
		}

		for (File f : list) {
			if (f.isDirectory()) {
				rtr.addAll(getFilesRegex(f, regex));
			} else {

				if (regex == null || regex.length == 0) {
					rtr.add(f);
				} else {
					for (String s : regex) {
						try {
							if (f.getAbsolutePath().matches(s)) {
								rtr.add(f);
								break;
							}
						} catch (Exception e) {

						}

					}
				}
			}
		}
		return rtr;
	}

	public TestSummary getSummary() {
		return mSummary;
	}

	public String getSummaryLog() {
		return mSummary.getSummaryLog();
	}

	public File getSummaryLogFile() {
		return new File(generateSummaryLogFilename(
				mPathInputFileDirectory.getAbsolutePath(), ""));
	}

	public File getPathSettings() {
		return mPathSettings;
	}

	public void setPathSettings(String pathSettings) {
		this.mPathSettings = new File(pathSettings);
	}

	public File getPathToolchain() {
		return mPathToolchain;
	}

	public void setPathToolchain(String pathToolchain) {
		this.mPathToolchain = new File(pathToolchain);
	}

	public File getPathInputFile() {
		return mPathInputFileDirectory;
	}

	public void setPathInputFile(String pathInputFileDirectory) {
		this.mPathInputFileDirectory = new File(pathInputFileDirectory);
	}

	public String[] getFileEndings() {
		return mFileEndings;
	}

	public void setFileEndings(String[] fileEndings) {
		this.mFileEndings = fileEndings;
	}

	public int getDeadline() {
		return mDeadline;
	}

	public void setDeadline(int deadline) {
		this.mDeadline = deadline;
	}

	@Override
	public String toString() {
		return mPathSettings.getName() + " " + mPathToolchain.getName() + " "
				+ mPathInputFileDirectory.getAbsolutePath();
	}

}
