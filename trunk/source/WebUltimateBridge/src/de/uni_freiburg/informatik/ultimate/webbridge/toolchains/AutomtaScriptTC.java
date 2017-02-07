/**
 * C TraceAbstraction toolchain.
 */
package de.uni_freiburg.informatik.ultimate.webbridge.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tool;
import de.uni_freiburg.informatik.ultimate.webbridge.website.WebToolchain;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks.TaskNames;

/**
 * @date 26.03.2013
 */
public class AutomtaScriptTC extends WebToolchain {

	@Override
	protected String defineDescription() {
		return NameStrings.TOOL_AUTOMATA_SCRIPT_INTERPRETER;
	}

	@Override
	protected String defineName() {
		return NameStrings.TOOL_AUTOMATA_SCRIPT_INTERPRETER;
	}

	@Override
	protected String defineId() {
		return "automataScript";
	}

	@Override
	protected TaskNames[] defineTaskName() {
		return new TaskNames[] { TaskNames.AUTOMATA_SCRIPT };
	}

	@Override
	protected String defineLanguage() {
		return "automata_script";
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
		final List<Tool> tools = new ArrayList<Tool>();
		
		tools.add(new Tool(PrefStrings.AUTOMATASCRIPTINTERPRETER));
		
		return tools;
	}

	@Override
	protected List<Setting> defineAdditionalSettings() {
		final List<Setting> rtr = new ArrayList<>();

		rtr.add(new Setting("/" + PrefStrings.AUTOMATASCRIPTINTERPRETER, Setting.SettingType.INTEGER, "Timeout",
				"10", true));

		return rtr;
	}

}
