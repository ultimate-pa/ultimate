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
		return PrefStrings.s_InterfaceLayoutFontsizeDefault;
	}

	@Override
	protected String defineInterfaceLayoutOrientation() {
		return PrefStrings.s_InterfaceLayoutOrientationDefault;
	}

	@Override
	protected String defineInterfaceLayoutTransitions() {
		return PrefStrings.s_InterfaceLayoutTransitionDefault;
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

		tools.add(new Tool(PrefStrings.s_syntaxchecker));
		tools.add(new Tool(PrefStrings.s_cacsl2boogietranslator));
		tools.addAll(BoogieTaipanTC.boogieTaipanTools());

		return tools;
	}

	private static List<Setting> cTaipanAdditionalSettings() {
		final List<Setting> settings = BoogieTaipanTC.boogieTaipanAdditionalSettings();
		settings.add(new Setting(PrefStrings.s_CACSL_LABEL_MemoryLeak, SettingType.BOOLEAN,
		        "Check for memory leak in main procedure", "false", true));
		settings.add(new Setting(PrefStrings.s_CACSL_LABEL_SignedIntegerOverflow, SettingType.BOOLEAN,
		        "Check for overflows of signed integers", "false", true));

		return settings;
	}

}
