package de.uni_freiburg.informatik.ultimatetest;

import java.io.File;
/**
 * A run of ultimate is defined by three files:
 * <ul> 
 * <li> an input file (e.g. an ANSI C file that is verified),
 * <li> a settings file, and
 * <li> a toolchain file.
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
		return "Input: " + m_Input + ", Settings: "
				+ m_Settings + ", Toolchain: " + m_Toolchain + "]";
	}
	
	
	
	

}
