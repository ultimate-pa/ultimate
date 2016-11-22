/**
 * Boogie TraceAbstraction toolchain.
 */
package de.uni_freiburg.informatik.ultimate.website.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.website.Setting;
import de.uni_freiburg.informatik.ultimate.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.website.Tool;
import de.uni_freiburg.informatik.ultimate.website.WebToolchain;

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
		return boogieAutomizerTools();
	}

	@Override
	protected List<Setting> defineAdditionalSettings() {
		return boogieAutomizerAdditionalSettings();
	}

	static List<Tool> boogieAutomizerTools() {
		final List<Tool> tools = new ArrayList<>();

		tools.add(new Tool(PrefStrings.s_boogiePreprocessor));
		tools.add(new Tool(PrefStrings.s_rcfgBuilder));
		tools.add(new Tool(PrefStrings.s_traceAbstraction));

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
