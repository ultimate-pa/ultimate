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
	private final File m_Input;
	private final File m_Settings;
	private final File m_Toolchain;

	public UltimateRunDefinition(File input, File settings, File toolchain) {
		super();
		if (input == null || toolchain == null) {
			throw new IllegalArgumentException("Toolchain and Input may not be null");
		}
		m_Input = input;
		m_Settings = settings;
		m_Toolchain = toolchain;
	}

	public File getInput() {
		return m_Input;
	}

	public File getSettings() {
		return m_Settings;
	}

	public File getToolchain() {
		return m_Toolchain;
	}

	@Override
	public String toString() {
		return generateShortStringRepresentation();
	}

	public String generateLongStringRepresentation() {
		return "Input: " + m_Input + ", Settings: " + m_Settings + ", Toolchain: " + m_Toolchain;
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
		result = prime * result + ((m_Input == null) ? 0 : m_Input.hashCode());
		result = prime * result + ((m_Settings == null) ? 0 : m_Settings.hashCode());
		result = prime * result + ((m_Toolchain == null) ? 0 : m_Toolchain.hashCode());
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
		if (m_Input == null) {
			if (other.m_Input != null)
				return false;
		} else if (!m_Input.equals(other.m_Input))
			return false;
		if (m_Settings == null) {
			if (other.m_Settings != null)
				return false;
		} else if (!m_Settings.equals(other.m_Settings))
			return false;
		if (m_Toolchain == null) {
			if (other.m_Toolchain != null)
				return false;
		} else if (!m_Toolchain.equals(other.m_Toolchain))
			return false;
		return true;
	}

}
