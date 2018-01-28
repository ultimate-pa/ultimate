/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.test;

import java.io.File;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase.AfterTest;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * A run of ultimate is defined by four things:
 * <ul>
 * <li>a list of input files (e.g. an ANSI C file that is verified),
 * <li>a settings file,
 * <li>a toolchain file, and
 * <li>a timeout in milliseconds.
 * </ul>
 *
 * @author heizmann@informatik.uni-freiburg.de
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class UltimateRunDefinition implements Comparable<UltimateRunDefinition> {
	private static final String[] PRIMARY_ENDINGS = new String[] { ".i", ".c", ".bpl", ".ats" };
	private static final String PATH_SEPARATOR = ";";
	private static final String NO_SETTINGS_NAME = "Default Settings";

	private final File[] mInput;
	private final File mSettings;
	private final File mToolchain;
	private final long mTimeout;
	private final AfterTest mFunAfterTest;

	private String mInputFilenames;

	public UltimateRunDefinition(final File input, final File settings, final File toolchain, final long timeout) {
		this(new File[] { input }, settings, toolchain, timeout);
	}

	public UltimateRunDefinition(final File input, final File settings, final File toolchain, final long timeout,
			final AfterTest funAfterTest) {
		this(new File[] { input }, settings, toolchain, timeout, funAfterTest);
	}

	public UltimateRunDefinition(final File[] input, final File settings, final File toolchain, final long timeout) {
		this(input, settings, toolchain, timeout, null);
	}

	public UltimateRunDefinition(final File[] input, final File settings, final File toolchain, final long timeout,
			final AfterTest funAfterTest) {
		if (input == null || toolchain == null) {
			throw new IllegalArgumentException("Toolchain and Input may not be null");
		}
		if (timeout < 0) {
			throw new IllegalArgumentException("Timeout must be larger or equal to 0");
		}
		mInput = input;
		mSettings = settings;
		mToolchain = toolchain;
		mTimeout = timeout;
		mFunAfterTest = funAfterTest;
	}

	public File[] getInput() {
		return mInput;
	}

	public File getSettings() {
		return mSettings;
	}

	public File getToolchain() {
		return mToolchain;
	}

	public long getTimeout() {
		return mTimeout;
	}

	public AfterTest getAfterTestMethod() {
		return mFunAfterTest;
	}

	public String getSettingsName() {
		return getSettings() == null ? NO_SETTINGS_NAME : getSettings().getName();
	}

	public String getSettingsAbsolutePath() {
		return getSettings() == null ? NO_SETTINGS_NAME : getSettings().getAbsolutePath();
	}

	/**
	 * This method tries to find the "primary" input file. This method is a hack to retain compatibility with the times
	 * were we only accepted one input file.
	 */
	public File selectPrimaryInputFile() {
		if (mInput.length == 1) {
			return mInput[0];
		}
		// DD: If we see multiple files here, we just select the first that ends in .i or .c. This is quite hacky,
		// but I do not see another option.
		final Optional<File> first = Arrays.stream(mInput)
				.filter(a -> Arrays.stream(PRIMARY_ENDINGS).anyMatch(ending -> a.getName().endsWith(ending)))
				.findFirst();
		if (first.isPresent()) {
			return first.get();
		}
		return null;
	}

	public String getInputFileNames() {
		if (mInputFilenames == null) {
			final StringBuilder sb = new StringBuilder();
			final File[] input = getInput();
			if (input.length == 1) {
				sb.append(removeTrunkExamplesPrefix(input[0].getAbsolutePath()));
			} else if (input.length > 1) {
				sb.append("[");
				sb.append(removeTrunkExamplesPrefix(input[0].getAbsolutePath()));
				for (int i = 1; i < input.length; ++i) {
					sb.append(PATH_SEPARATOR);
					sb.append(removeTrunkExamplesPrefix(input[i].getAbsolutePath()));
				}
				sb.append("]");
			}
			mInputFilenames = sb.toString();
		}
		return mInputFilenames;
	}

	/**
	 * Returns a string describing the folders from which the input files come.
	 *
	 * @return
	 */
	public String getInputFileFolders() {
		final StringBuilder sb = new StringBuilder();
		final File[] input = getInput();
		final Set<String> set = new HashSet<>();
		if (input.length == 1) {
			sb.append(removeTrunkExamplesPrefix(input[0].getParent()));
		} else if (input.length > 1) {
			sb.append("[");
			String path = removeTrunkExamplesPrefix(input[0].getParent());
			set.add(path);
			sb.append(path);
			for (int i = 1; i < input.length; ++i) {
				path = removeTrunkExamplesPrefix(input[i].getParent());
				if (set.add(path)) {
					sb.append(PATH_SEPARATOR);
					sb.append(path);
				}
			}
			sb.append("]");
		}
		return sb.toString();
	}

	@Override
	public String toString() {
		return generateShortStringRepresentation();
	}

	public String generateLongStringRepresentation() {
		return "Input: " + mInput + ", Settings: " + mSettings + ", Toolchain: " + mToolchain;
	}

	public String generateShortStringRepresentation() {
		final StringBuilder sb = new StringBuilder();
		final File settings = getSettings();
		final File toolchain = getToolchain();
		sb.append("Input:").append(getInputFileNames());
		sb.append(" Settings:");
		if (settings == null) {
			sb.append("default");
		} else {
			sb.append(removeTrunkExamplesPrefix(settings.getAbsolutePath()));
		}
		sb.append(" Toolchain:");
		sb.append(removeTrunkExamplesPrefix(toolchain.getAbsolutePath()));
		if (CoreUtil.OS_IS_WINDOWS) {
			return sb.toString().replaceAll("\\\\", "/");
		}
		return sb.toString();
	}

	public static String removeTrunkExamplesPrefix(final String path) {
		final String trunk = TestUtil.getPathFromTrunk("");
		final String examples = trunk + File.separator + "examples" + File.separator;
		final int lastIndexOf = path.lastIndexOf(examples);
		if (lastIndexOf != -1) {
			final String trunkated = path.substring(lastIndexOf + examples.length(), path.length());
			return trunkated;
		}
		return path;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (mInput == null ? 0 : Arrays.hashCode(mInput));
		result = prime * result + (mSettings == null ? 0 : mSettings.hashCode());
		result = prime * result + (mToolchain == null ? 0 : mToolchain.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final UltimateRunDefinition other = (UltimateRunDefinition) obj;
		if (mInput == null) {
			if (other.mInput != null) {
				return false;
			}
		} else if (!Arrays.equals(mInput, other.mInput)) {
			return false;
		}
		if (mSettings == null) {
			if (other.mSettings != null) {
				return false;
			}
		} else if (!mSettings.equals(other.mSettings)) {
			return false;
		}
		if (mToolchain == null) {
			if (other.mToolchain != null) {
				return false;
			}
		} else if (!mToolchain.equals(other.mToolchain)) {
			return false;
		}
		return true;
	}

	@Override
	public int compareTo(final UltimateRunDefinition other) {
		if (other.mInput.length > mInput.length) {
			return -1;
		} else if (other.mInput.length < mInput.length) {
			return 1;
		} else {
			for (int i = 0; i < mInput.length; ++i) {
				final int inputCmp = mInput[i].compareTo(other.mInput[i]);
				if (inputCmp != 0) {
					return inputCmp;
				}
			}
		}

		final int tcCmp = mToolchain.compareTo(other.mToolchain);
		if (tcCmp != 0) {
			return tcCmp;
		}

		if (mSettings == null && other.mSettings == null) {
			return 0;
		} else if (mSettings == null) {
			return 1;
		} else if (other.mSettings == null) {
			return -1;
		} else {
			return mSettings.compareTo(other.mSettings);
		}
	}
}
