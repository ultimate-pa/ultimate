package de.uni_freiburg.informatik.ultimatetest;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FilenameFilter;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Set;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;

public class SVCOMP14TestDescriptor extends UltimateTestDescriptor {

	private static final int NORESULT = 0;
	private static final int CORRECT = 1;
	private static final int UNPROVABLE = 2;
	private static final int TIMEOUT = 3;
	private static final int INCORRECT = 4;
	private static final int SYNTAXERROR = 5;

	private boolean mShouldBeSafe;

	public SVCOMP14TestDescriptor(String mPathSettings, String mPathToolchain,
			String mPathInputFileDirectory, int mDeadline, String categoryName,
			String summaryLogFilename, boolean shouldbesafe, String description) {
		super(new File(mPathSettings), new File(mPathToolchain), new File(
				mPathInputFileDirectory), new String[] { ".c", ".i" },
				mDeadline, new SVCOMP14TestSummary(categoryName,
						summaryLogFilename), description);
		mShouldBeSafe = shouldbesafe;
	}

	public SVCOMP14TestDescriptor(File pathSettings, File pathToolchain,
			File pathInputFile, String[] fileEndings, int deadline,
			TestSummary summary, boolean shouldbesafe, String description) {
		super(pathSettings, pathToolchain, pathInputFile, fileEndings,
				deadline, summary, description);
		mShouldBeSafe = shouldbesafe;
	}

	@Override
	public UltimateTestDescriptor copy() {
		return new SVCOMP14TestDescriptor(getPathSettings(),
				getPathToolchain(), getPathInputFile(), getFileEndings(),
				getDeadline(), mSummary, mShouldBeSafe, mDescription);
	}

	@Override
	public UltimateTestDescriptor copy(String pathToFile) {
		return new SVCOMP14TestDescriptor(getPathSettings(),
				getPathToolchain(), new File(pathToFile), getFileEndings(),
				getDeadline(), mSummary, mShouldBeSafe, mDescription);
	}

	@Override
	public boolean isResultFail(Set<Entry<String, List<IResult>>> resultMap) {
		SVCOMP14TestSummary summary = (SVCOMP14TestSummary) mSummary;
		Set<Entry<String, List<IResult>>> resultSet = UltimateServices
				.getInstance().getResultMap().entrySet();

		if (resultSet.isEmpty()) {
			summary.addFail(null, getPathInputFile().getAbsolutePath(),
					"There was no result");
			return true;
		}

		// FIXME: This is cutnpaste from result notifier ... the whole
		// UltimateTest is very dirty, so it may be ok... but in the long run we
		// need to find another way

		int toolchainResult = NORESULT;

		IResult finalResult = null;

		for (Entry<String, List<IResult>> results : resultSet) {
			List<IResult> resultList = results.getValue();
			for (IResult result : resultList) {
				if (result instanceof SyntaxErrorResult) {
					toolchainResult = SYNTAXERROR;
					finalResult = result;
				} else if (result instanceof UnprovableResult) {
					if (toolchainResult < UNPROVABLE) {
						toolchainResult = UNPROVABLE;
						finalResult = result;
					}
				} else if (result instanceof CounterExampleResult) {
					if (toolchainResult < INCORRECT) {
						toolchainResult = INCORRECT;
						finalResult = result;
					}
				} else if (result instanceof PositiveResult) {
					if (toolchainResult < CORRECT) {
						toolchainResult = CORRECT;
						finalResult = result;
					}
				} else if (result instanceof TimeoutResult) {
					if (toolchainResult < TIMEOUT) {
						toolchainResult = TIMEOUT;
						finalResult = result;
					}
				}
			}
		}
		switch (toolchainResult) {
		case SYNTAXERROR:
		case UNPROVABLE:
		case TIMEOUT:
		case NORESULT:
			summary.addUnknown(finalResult, getPathInputFile()
					.getAbsolutePath(), finalResult.getLongDescription());
			return true;
		case INCORRECT:
			if (mShouldBeSafe) {
				summary.addFail(finalResult, getPathInputFile()
						.getAbsolutePath(), "SHOULD BE SAFE! Real message is: "
						+ finalResult.getLongDescription());
			} else {
				summary.addSuccess(finalResult, getPathInputFile()
						.getAbsolutePath(), finalResult.getLongDescription());
			}

			return true;
		case CORRECT:
			if (mShouldBeSafe) {
				summary.addSuccess(finalResult, getPathInputFile()
						.getAbsolutePath(), finalResult.getLongDescription());
			} else {
				summary.addFail(
						finalResult,
						getPathInputFile().getAbsolutePath(),
						"SHOULD BE UNSAFE! Real message is: "
								+ finalResult.getLongDescription());
			}

			return false;

		default:
			throw new AssertionError("unknown result");
		}

	}

	public static SVCOMP14TestDescriptor[] createDescriptorsFromSVCOMPRootDirectory(
			String svcomproot, HashMap<String, String> categoryToSettingsMap,
			String toolchainPath, int deadline, String description)
			throws Exception {

		// get all set files
		File root = new File(svcomproot);
		File[] setFiles = root.listFiles(new FilenameFilter() {

			@Override
			public boolean accept(File arg0, String arg1) {
				return arg1.endsWith(".set");
			}
		});

		// get all C files
		ArrayList<File> singleFiles = new ArrayList<File>();
		singleFiles.addAll(UltimateTestDescriptor.getFilesRegex(root,
				new String[] { ".*\\.c", ".*\\.i" }));

		ArrayList<SVCOMP14TestDescriptor> descriptors = new ArrayList<SVCOMP14TestDescriptor>();

		// create for each file in each set a descriptor; the set of descriptors
		// for a category should share a summary instance
		for (File setFile : setFiles) {
			String categoryName = setFile.getName().replace(".set", "");

			if (!categoryToSettingsMap.containsKey(categoryName)) {
				continue;
			}

			ArrayList<File> currentFiles = new ArrayList<File>();
			String summaryLogfileName = generateSummaryLogFilename(svcomproot,
					description + " " + categoryName);
			SVCOMP14TestSummary summary = new SVCOMP14TestSummary(categoryName,
					summaryLogfileName);
			try {
				DataInputStream in = new DataInputStream(new FileInputStream(
						setFile));
				BufferedReader br = new BufferedReader(
						new InputStreamReader(in));
				String line;
				while ((line = br.readLine()) != null) {
					if (line.isEmpty()) {
						continue;
					}
					String regex = ".*"
							+ line.replace(".", "\\.").replace("*", ".*");
					currentFiles.addAll(filter(singleFiles, regex));
				}
				in.close();
			} catch (Exception e) {
				e.printStackTrace();
			}

			for (File singleFile : currentFiles) {
				boolean shouldbesafe = singleFile.getName().contains("true");
				if (!shouldbesafe) {
					if (!singleFile.getName().contains("false")) {
						throw new Exception("Should contain false");
					}
				}

				SVCOMP14TestDescriptor descriptor = new SVCOMP14TestDescriptor(
						categoryToSettingsMap.get(categoryName), toolchainPath,
						singleFile.getAbsolutePath(), deadline, categoryName,
						summaryLogfileName, shouldbesafe, description);
				descriptor.mSummary = summary;
				descriptors.add(descriptor);
			}
		}

		return descriptors.toArray(new SVCOMP14TestDescriptor[descriptors
				.size()]);

	}

	private static Collection<File> filter(Collection<File> files, String regex) {
		ArrayList<File> singleFiles = new ArrayList<File>();

		for (File f : files) {
			String path = f.getAbsolutePath().replaceAll("\\\\", "/");
			if (path.matches(regex)) {
				singleFiles.add(f);
			}
		}

		return singleFiles;
	}

}
