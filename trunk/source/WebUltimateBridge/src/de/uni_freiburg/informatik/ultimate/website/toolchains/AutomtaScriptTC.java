/**
 * C TraceAbstraction toolchain.
 */
package de.uni_freiburg.informatik.ultimate.website.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.website.Setting;
import de.uni_freiburg.informatik.ultimate.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.website.Tool;
import de.uni_freiburg.informatik.ultimate.website.WebToolchain;

/**
 * @date 26.03.2013
 */
public class AutomtaScriptTC extends WebToolchain {

	@Override
	protected String defineDescription() {
		return NameStrings.s_TOOL_AutomataScriptInterpreter;
	}

	@Override
	protected String defineName() {
		return NameStrings.s_TOOL_AutomataScriptInterpreter;
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
		return "automata script";
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
		List<Tool> tools = new ArrayList<Tool>();
		
		tools.add(new Tool(PrefStrings.s_automatascriptinterpreter));
		
		return tools;
	}

	@Override
	protected List<Setting> defineAdditionalSettings() {
		List<Setting> rtr = new ArrayList<>();

		rtr.add(new Setting("/" + PrefStrings.s_automatascriptinterpreter, Setting.SettingType.INTEGER, "Timeout",
				"10", true));

		return rtr;
	}

}
