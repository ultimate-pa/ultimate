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
 * @author Matthias Heizmann
 */
public class BoogieConcurrentTraceAbstractionTC extends WebToolchain {

	@Override
	protected String defineDescription() {
		return NameStrings.TOOL_AUTOMIZER_CONCURRENT;
	}

	@Override
	protected String defineName() {
		return NameStrings.TOOL_AUTOMIZER_CONCURRENT;
	}

	@Override
	protected String defineId() {
		return "boogieConcurrentTraceAbstr";
	}
	
	@Override
	protected String defineUserInfo() {
		return "Convention: we use the procedure ~init to initialize global variables, each other procedure is considered as a thread of a concurrent system";
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
	protected TaskNames[] defineTaskName() {
		return new TaskNames[] { TaskNames.CONCURRENT_TRACE_ABSTRACTION_BOOGIE };
	}

	@Override
	protected String defineLanguage() {
		return "boogie";
	}

	@Override
	protected List<Tool> defineTools() {
		final List<Tool> tools = new ArrayList<Tool>();

		tools.add(new Tool(PrefStrings.s_boogiePreprocessor));
		tools.add(new Tool(PrefStrings.s_rcfgBuilder));
		tools.add(new Tool(PrefStrings.s_traceAbstractionConcurrent));
		
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
		return "TraceAbstractionConcurrent.epf";
	}

}
