package de.uni_freiburg.informatik.ultimate.webbridge.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tool;
import de.uni_freiburg.informatik.ultimate.webbridge.website.WebToolchain;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @author Matthias Heizmann
 */
public class BoogieConcurrentTraceAbstractionTC extends WebToolchain {

	@Override
	protected String defineDescription() {
		return NameStrings.TOOL_AUTOMIZER_PETRI;
	}

	@Override
	protected String defineName() {
		return NameStrings.TOOL_AUTOMIZER_PETRI;
	}

	@Override
	protected String defineId() {
		return "boogieConcurrentTraceAbstr";
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
	protected TaskNames[] defineTaskName() {
		return new TaskNames[] { TaskNames.CONCURRENT_BOOGIE };
	}

	@Override
	protected String defineLanguage() {
		return "boogie";
	}

	@Override
	protected List<Tool> defineTools() {
		final List<Tool> tools = new ArrayList<Tool>();

		tools.add(new Tool(PrefStrings.BOOGIE_PREPROCESSOR));
		tools.add(new Tool(PrefStrings.BOOGIE_PROCEDURE_INLINER));
		tools.add(new Tool(PrefStrings.RCFGBUILDER));
		tools.add(new Tool(PrefStrings.TRACE_ABSTRACTION_CONCURRENT));

		return tools;
	}

	@Override
	protected List<Setting> defineAdditionalSettings() {
		final List<Setting> rtr = new ArrayList<>();
//		rtr.add(new Setting(PrefStrings.s_RCFG_LABEL_BlockSize, "Size of a code block",
//				new String[] { PrefStrings.s_RCFG_VALUE_Single }, false,
//				new String[] { PrefStrings.s_RCFG_VALUE_Single, PrefStrings.s_RCFG_VALUE_Seq,
//						PrefStrings.s_RCFG_VALUE_Block }, true));
		return rtr;
	}

	@Override
	protected String defineToolchainSettingsFile() {
		return "PetriAutomizer-default.epf";
	}

}
