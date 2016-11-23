package de.uni_freiburg.informatik.ultimate.website.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.website.Setting;
import de.uni_freiburg.informatik.ultimate.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.website.Tool;
import de.uni_freiburg.informatik.ultimate.website.WebToolchain;

/**
 * Boogie Taipan toolchain.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 */
public class BoogieTaipanTC extends WebToolchain {

	@Override
	protected String defineDescription() {
		return NameStrings.s_TOOL_Taipan;
	}

	@Override
	protected String defineName() {
		return NameStrings.s_TOOL_Taipan;
	}

	@Override
	protected String defineId() {
		return "boogieTaipan";
	}

	@Override
	protected TaskNames[] defineTaskName() {
		return new TaskNames[] { TaskNames.TAIPAN_BOOGIE };
	}

	@Override
	protected String defineLanguage() {
		return "boogie";
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
		return boogieTaipanTools();
	}

	@Override
	protected List<Setting> defineAdditionalSettings() {
		return boogieTaipanAdditionalSettings();
	}

	static List<Tool> boogieTaipanTools() {
		final List<Tool> tools = new ArrayList<>();

		tools.add(new Tool(PrefStrings.s_boogiePreprocessor));
		tools.add(new Tool(PrefStrings.s_rcfgBuilder));
		tools.add(new Tool(PrefStrings.s_traceAbstraction));

		return tools;
	}

	static List<Setting> boogieTaipanAdditionalSettings() {
		final List<Setting> rtr = new ArrayList<>();

		// rtr.add(new Setting(PrefStrings.s_TA_LABEL_Hoare, Setting.SettingType.BOOLEAN, "Compute Hoare Annotation",
		// "true", true));

		return rtr;
	}

	@Override
	protected String defineToolchainSettingsFile() {
		return "Taipan.epf";
	}

}
