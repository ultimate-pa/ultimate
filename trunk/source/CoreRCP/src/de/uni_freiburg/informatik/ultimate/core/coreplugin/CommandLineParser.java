package de.uni_freiburg.informatik.ultimate.core.coreplugin;

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
	private static final String s_PLUGIN_ID = "de.uni_freiburg.informatik.ultimate.core.coreplugin.CommandLineParser";

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
