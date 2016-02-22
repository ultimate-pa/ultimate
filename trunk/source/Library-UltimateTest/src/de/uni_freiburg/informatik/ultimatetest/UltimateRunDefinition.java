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
package de.uni_freiburg.informatik.ultimatetest;

import java.io.File;
import de.uni_freiburg.informatik.ultimatetest.util.TestUtil;

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
public class UltimateRunDefinition implements Comparable<UltimateRunDefinition> {
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
		String trunk = TestUtil.getPathFromTrunk("");
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

	@Override
	public int compareTo(final UltimateRunDefinition other) {
		int inputCmp = mInput.compareTo(other.mInput);
		if (inputCmp != 0) {
			return inputCmp;
		}
		int tcCmp = mToolchain.compareTo(other.mToolchain);
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
