/**
 * Boogie TraceAbstraction toolchain.
 */
package de.uni_freiburg.informatik.ultimate.webbridge.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tool;
import de.uni_freiburg.informatik.ultimate.webbridge.website.WebToolchain;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks.TaskNames;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 14.02.2012
 */
public class BoogieAutomizerTC extends WebToolchain {

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
		return "boogieAutomizer";
	}

	@Override
	protected TaskNames[] defineTaskName() {
		return new TaskNames[] { TaskNames.AUTOMIZER_BOOGIE };
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
		return boogieAutomizerTools();
	}

	@Override
	protected List<Setting> defineAdditionalSettings() {
		return boogieAutomizerAdditionalSettings();
	}

	static List<Tool> boogieAutomizerTools() {
		final List<Tool> tools = new ArrayList<>();

		tools.add(new Tool(PrefStrings.BOOGIE_PREPROCESSOR));
		tools.add(new Tool(PrefStrings.RCFGBUILDER));
		tools.add(new Tool(PrefStrings.TRACE_ABSTRACTION));

		return tools;
	}

	static List<Setting> boogieAutomizerAdditionalSettings() {
		final List<Setting> rtr = new ArrayList<>();

		// rtr.add(new Setting(PrefStrings.s_TA_LABEL_Hoare, Setting.SettingType.BOOLEAN, "Compute Hoare Annotation",
		// "true", true));

		return rtr;
	}

	@Override
	protected String defineToolchainSettingsFile() {
		return "Automizer.epf";
	}

}
