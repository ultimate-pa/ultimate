package de.uni_freiburg.informatik.ultimate.webbridge.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tool;
import de.uni_freiburg.informatik.ultimate.webbridge.website.WebToolchain;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting.SettingType;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks.TaskNames;

/**
 * C Taipan toolchain.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 */
public class CTaipanTC extends WebToolchain {

	@Override
	protected String defineDescription() {
		return NameStrings.TOOL_TAIPAN;
	}

	@Override
	protected String defineName() {
		return NameStrings.TOOL_TAIPAN;
	}

	@Override
	protected String defineId() {
		return "cTaipan";
	}

	@Override
	protected TaskNames[] defineTaskName() {
		return new TaskNames[] { TaskNames.TAIPAN_C };
	}

	@Override
	protected String defineUserInfo() {
		return null;
	}

	@Override
	protected String defineInterfaceLayoutFontsize() {
		return PrefStrings.INTERFACE_LAYOUT_FONTSIZE_DEFAULT;
	}

	@Override
	protected String defineInterfaceLayoutOrientation() {
		return PrefStrings.INTERFACE_LAYOUT_ORIENTATION_DEFAULT;
	}

	@Override
	protected String defineInterfaceLayoutTransitions() {
		return PrefStrings.INTERFACE_LAYOUT_TRANSITION_DEFAULT;
	}

	@Override
	protected List<Tool> defineTools() {
		return cTaipanTools();
	}

	@Override
	protected List<Setting> defineAdditionalSettings() {
		return cTaipanAdditionalSettings();
	}

	@Override
	protected String defineToolchainSettingsFile() {
		return "Taipan.epf";
	}

	@Override
	protected String defineLanguage() {
		return "c";
	}

	private static List<Tool> cTaipanTools() {
		final List<Tool> tools = new ArrayList<>();

		tools.add(new Tool(PrefStrings.SYNTAXCHECKER));
		tools.add(new Tool(PrefStrings.CACSL2BOOGIETRANSLATOR));
		tools.addAll(BoogieTaipanTC.boogieTaipanTools());

		return tools;
	}

	private static List<Setting> cTaipanAdditionalSettings() {
		final List<Setting> settings = BoogieTaipanTC.boogieTaipanAdditionalSettings();
		settings.add(new Setting(PrefStrings.CACSL_LABEL_MEMORY_LEAK, SettingType.BOOLEAN,
		        "Check for memory leak in main procedure", "false", true));
		settings.add(new Setting(PrefStrings.CACSL_LABEL_SIGNED_INTEGER_OVERFLOW, SettingType.BOOLEAN,
		        "Check for overflows of signed integers", "false", true));

		return settings;
	}

}
