/**
 * Boogie TraceAbstraction toolchain.
 */
package de.uni_freiburg.informatik.ultimate.webbridge.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tool;
import de.uni_freiburg.informatik.ultimate.webbridge.website.WebToolchain;

/**
 * @author @author Matthias Heizmann
 */
public class CRefereeTC extends WebToolchain {

	@Override
	protected String defineDescription() {
		return NameStrings.TOOL_REFEREE;
	}

	@Override
	protected String defineName() {
		return NameStrings.TOOL_REFEREE;
	}

	@Override
	protected String defineId() {
		return "cReferee";
	}

	@Override
	protected TaskNames[] defineTaskName() {
		return new TaskNames[] { TaskNames.REFEREE_C };
	}

	@Override
	protected String defineLanguage() {
		return "c";
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
		return cRefereeTools();
	}

	@Override
	protected List<Setting> defineAdditionalSettings() {
		return boogieAutomizerAdditionalSettings();
	}

	static List<Tool> cRefereeTools() {
		final List<Tool> tools = new ArrayList<>();

		tools.add(new Tool(PrefStrings.SYNTAXCHECKER));
		tools.add(new Tool(PrefStrings.CACSL2BOOGIETRANSLATOR));
		tools.add(new Tool(PrefStrings.BOOGIE_PROCEDURE_INLINER));
		tools.addAll(BoogieRefereeTC.boogieRefereeTools());

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
		return "Referee.epf";
	}

}
