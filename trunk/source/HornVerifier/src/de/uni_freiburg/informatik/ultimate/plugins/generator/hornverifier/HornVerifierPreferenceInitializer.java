package de.uni_freiburg.informatik.ultimate.plugins.generator.hornverifier;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;

/**
 * Initializer and container of preferences for the horn verifier plugin.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class HornVerifierPreferenceInitializer extends UltimatePreferenceInitializer {

	public static final String LABEL_DUMP_TO_FILE = "Dump SMT-script to file";
	private static final boolean DEF_DUMP_TO_FILE = false;

	public static final String LABEL_DUMP_DIR = "Path to dump script";
	private static final String DEF_DUMP_DIR = "";

	public HornVerifierPreferenceInitializer() {
		super(Activator.PLUGIN_ID, "Horn Verifier");
	}

	@Override
	protected BaseUltimatePreferenceItem[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>(LABEL_DUMP_TO_FILE, DEF_DUMP_TO_FILE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_DUMP_DIR, DEF_DUMP_DIR, PreferenceType.Directory) };
	}
}
