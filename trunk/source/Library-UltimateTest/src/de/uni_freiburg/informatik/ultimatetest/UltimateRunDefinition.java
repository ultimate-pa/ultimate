package de.uni_freiburg.informatik.ultimatetest;

import java.io.File;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * A run of ultimate is defined by three files:
 * <ul>
 * <li>an input file (e.g. an ANSI C file that is verified),
 * <li>a settings file, and
 * <li>a toolchain file.
 * </ul>
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class UltimateRunDefinition {
	private final File mInput;
	private final File mSettings;
	private final File mToolchain;

	public UltimateRunDefinition(File input, File settings, File toolchain) {
		super();
		if (input == null || toolchain == null) {
			throw new IllegalArgumentException("Toolchain and Input may not be null");
		}
		mInput = input;
		mSettings = settings;
		mToolchain = toolchain;
	}

	public File getInput() {
		return mInput;
	}

	public File getSettings() {
		return mSettings;
	}

	public File getToolchain() {
		return mToolchain;
	}

	@Override
	public String toString() {
		return generateShortStringRepresentation();
	}

	public String generateLongStringRepresentation() {
		return "Input: " + mInput + ", Settings: " + mSettings + ", Toolchain: " + mToolchain;
	}

	public String generateShortStringRepresentation() {
		StringBuilder sb = new StringBuilder();
		sb.append("Input:");
		sb.append(removeTrunkExamplesPrefix(getInput().getAbsolutePath()));
		sb.append(" Settings:");
		if (getSettings() == null) {
			sb.append("default");
		} else {
			sb.append(removeTrunkExamplesPrefix(getSettings().getAbsolutePath()));
		}
		sb.append(" Toolchain:");
		sb.append(removeTrunkExamplesPrefix(getToolchain().getAbsolutePath()));
		return sb.toString();
	}

	public String removeTrunkExamplesPrefix(String path) {
		String trunk = Util.getPathFromTrunk("");
		String examples = trunk + File.separator + "examples" + File.separator;
		int lastIndexOf = path.lastIndexOf(examples);
		if (lastIndexOf != -1) {
			String trunkated = path.substring(lastIndexOf + examples.length(), path.length());
			return trunkated;
		} else {
			return path;
		}
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mInput == null) ? 0 : mInput.hashCode());
		result = prime * result + ((mSettings == null) ? 0 : mSettings.hashCode());
		result = prime * result + ((mToolchain == null) ? 0 : mToolchain.hashCode());
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
		UltimateRunDefinition other = (UltimateRunDefinition) obj;
		if (mInput == null) {
			if (other.mInput != null)
				return false;
		} else if (!mInput.equals(other.mInput))
			return false;
		if (mSettings == null) {
			if (other.mSettings != null)
				return false;
		} else if (!mSettings.equals(other.mSettings))
			return false;
		if (mToolchain == null) {
			if (other.mToolchain != null)
				return false;
		} else if (!mToolchain.equals(other.mToolchain))
			return false;
		return true;
	}

}
