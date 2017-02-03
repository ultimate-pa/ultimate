/**
 * C TraceAbstraction toolchain.
 */
package de.uni_freiburg.informatik.ultimate.webbridge.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tool;
import de.uni_freiburg.informatik.ultimate.webbridge.website.WebToolchain;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting.SettingType;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks.TaskNames;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @author Matthias Heizmann
 * @date 14.02.2012
 */
public class CAutomizerTC extends WebToolchain {

	@Override
	protected String defineDescription() {
		return NameStrings.TOOL_AUTOMIZER;
	}

	@Override
	protected String defineName() {
		return NameStrings.TOOL_AUTOMIZER;
	}

	@Override
	protected String defineId() {
		return "cAutomizer";
	}

	@Override
	protected TaskNames[] defineTaskName() {
		return new TaskNames[] { TaskNames.AUTOMIZER_C };
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
		final List<Tool> tools = new ArrayList<>();

		tools.add(new Tool(PrefStrings.s_syntaxchecker));
		tools.add(new Tool(PrefStrings.s_cacsl2boogietranslator));
		tools.addAll(BoogieAutomizerTC.boogieAutomizerTools());

		return tools;
	}

	@Override
	protected List<Setting> defineAdditionalSettings() {
		final List<Setting> rtr = BoogieAutomizerTC.boogieAutomizerAdditionalSettings();
		rtr.add(new Setting(PrefStrings.s_CACSL_LABEL_MemoryLeak, SettingType.BOOLEAN,
				"Check for memory leak in main procedure", "false", true));
		rtr.add(new Setting(PrefStrings.s_CACSL_LABEL_SignedIntegerOverflow, SettingType.BOOLEAN,
				"Check for overflows of signed integers", "false", true));
		return rtr;
	}

	@Override
	protected String defineToolchainSettingsFile() {
		return "Automizer.epf";
	}

	@Override
	protected String defineLanguage() {
		return "c";
	}
}
