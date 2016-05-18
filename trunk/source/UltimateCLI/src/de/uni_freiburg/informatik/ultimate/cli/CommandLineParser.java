/*
 * Copyright (C) 2009-2015 Christian Simon
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cli;

import java.util.ArrayList;

/**
 * A rudimentary parser for the Ultimate command-line.
 * 
 * @author Christian Simon
 * 
 */
public class CommandLineParser {

	private boolean mInteractiveMode = false;
	private boolean mConsoleMode = false;
	private boolean mExit = false;
	private String mPreludeFile = null;
	private String mToolchainFile;
	private String[] mInputFiles;
	private String mSettingsFile;

	private static final String s_PLUGIN_NAME = "Command Line Parser";
	private static final String s_PLUGIN_ID = "de.uni_freiburg.informatik.ultimate.core.model.coreplugin.CommandLineParser";

	public CommandLineParser() {

	}

	public void printUsage() {
		System.err.println("Ultimate Command Line Usage:");
		System.err
				.println("./Ultimate --help | --console [<toolchain file> <input file>+ [--prelude <file>] [--settings <file>]] ");
		System.err.println("No argument will run Ultimate in GUI mode.");
		System.err.println("Only the --console argument will run Ultimate in interactive command-line mode.");
		System.err.println("Your parsed arguments were:");
		System.err.println("Prelude File:" + mPreludeFile);
		System.err.println("Tool File:" + mToolchainFile);
		System.err.println("Input File:" + mInputFiles);
		System.err.println("Settings file:" + mSettingsFile);
		System.err.println("Console mode:" + String.valueOf(mConsoleMode));
		System.err.println("Interactive mode:" + String.valueOf(mInteractiveMode));
		System.err.println("Exit Switch:" + String.valueOf(mExit));
	}

	public void parse(String[] args) {
		int argc = args.length;

		// iterate over command lines
		for (int i = 0; i < argc; i++) {

			if (args[i].compareTo("--help") == 0) {
				mExit = true;
				return;
			}

			if (args[i].compareTo("--console") == 0) {
				mConsoleMode = true;
				mInteractiveMode = true;
				continue;
			}

			if (mConsoleMode == true && mToolchainFile == null && mPreludeFile == null) {
				mInteractiveMode = false;
				// Now get the two remaining files
				try {
					mToolchainFile = new String(args[i]);
					++i;
					ArrayList<String> inputFiles = new ArrayList<>();
					while (i < args.length) {
						String current = args[i];
						if (current.startsWith("--")) {
							--i;
							break;
						}
						inputFiles.add(current);
						++i;
					}
					if (inputFiles.isEmpty()) {
						mExit = true;
						return;
					} else {
						mInputFiles = inputFiles.toArray(new String[0]);
					}
					continue;
				} catch (Exception e) {
					mExit = true;
					return;
				}
			}
			// parse the optional prelude file
			if (mConsoleMode == true && mToolchainFile != null && mInputFiles != null) {

				if (args[i].compareTo("--prelude") == 0) {
					try {
						mPreludeFile = args[++i];
						return;
					} catch (Exception e) {
						mExit = true;
						return;
					}
				}
				if (args[i].compareTo("--settings") == 0) {
					try {
						mSettingsFile = args[++i];
					} catch (Exception e) {
						mExit = true;
						return;
					}
				}
			}
		}
	}

	public String getToolFile() {
		return mToolchainFile;
	}

	public String[] getInputFile() {
		return mInputFiles;
	}

	public String getPreludeFile() {
		return mPreludeFile;
	}

	public boolean getExitSwitch() {
		return mExit;
	}

	public boolean getConsoleSwitch() {
		return mConsoleMode;
	}

	public boolean getInteractiveSwitch() {
		return mInteractiveMode;
	}

	public String getName() {
		return s_PLUGIN_NAME;
	}

	public String getPluginID() {
		return s_PLUGIN_ID;
	}

	public String getSettings() {
		return mSettingsFile;
	}

}
