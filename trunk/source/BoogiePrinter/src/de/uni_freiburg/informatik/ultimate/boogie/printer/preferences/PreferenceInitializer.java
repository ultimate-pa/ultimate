package de.uni_freiburg.informatik.ultimate.boogie.printer.preferences;

import de.uni_freiburg.informatik.ultimate.boogie.printer.Activator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;

public class PreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		// TODO Auto-generated method stub
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<String>(DUMP_PATH_LABEL,
						DUMP_PATH_DEFAULT, PreferenceType.Directory),
				new UltimatePreferenceItem<String>(FILE_NAME_LABEL,
						FILE_NAME_DEFAULT, PreferenceType.String),
				new UltimatePreferenceItem<Boolean>(
						SAVE_IN_SOURCE_DIRECTORY_LABEL,
						SAVE_IN_SOURCE_DIRECTORY_DEFAULT,
						PreferenceType.Boolean), 
						new UltimatePreferenceItem<Boolean>(
								UNIQUE_NAME_LABEL,
								UNIQUE_NAME_DEFAULT,
								PreferenceType.Boolean), 
								
		};
	}

	@Override
	protected String getPlugID() {
		return Activator.s_PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "Boogie Printer";
	}

	public static String getDumpPath() {
		return new UltimatePreferenceStore(Activator.s_PLUGIN_ID)
				.getString(DUMP_PATH_LABEL);
	}

	public static String getFilename() {
		return new UltimatePreferenceStore(Activator.s_PLUGIN_ID)
				.getString(FILE_NAME_LABEL);
	}

	public static boolean getUseUniqueFilename() {
		return new UltimatePreferenceStore(Activator.s_PLUGIN_ID)
				.getBoolean(UNIQUE_NAME_LABEL);
	}

	public static boolean getSaveInSourceDirectory() {
		return new UltimatePreferenceStore(Activator.s_PLUGIN_ID)
				.getBoolean(SAVE_IN_SOURCE_DIRECTORY_LABEL);
	}

	private static final String SAVE_IN_SOURCE_DIRECTORY_LABEL = "Save file in source directory?";
	private static final boolean SAVE_IN_SOURCE_DIRECTORY_DEFAULT = false;

	private static final String UNIQUE_NAME_LABEL = "Use automatic naming?";
	private static final boolean UNIQUE_NAME_DEFAULT = false;

	private static final String DUMP_PATH_LABEL = "Dump path:";
	private static final String DUMP_PATH_DEFAULT = System
			.getProperty("java.io.tmpdir");

	private static final String FILE_NAME_LABEL = "File name:";
	private static final String FILE_NAME_DEFAULT = "boogiePrinter.bpl";

}
