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
		return "Concurrent trace abstraction toolchain";
	}

	@Override
	protected String defineName() {
		return "Concurrent Trace Abstraction";
	}

	@Override
	protected String defineId() {
		return "boogieConcurrentTraceAbstr";
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
		List<Tool> tools = new ArrayList<Tool>();

		tools.add(new Tool(PrefStrings.s_boogiePreprocessor));
		tools.add(new Tool(PrefStrings.s_rcfgBuilder));
		tools.add(new Tool(PrefStrings.s_traceAbstractionConcurrent));
		
		return tools;
	}

	@Override
	protected List<Setting> defineAdditionalSettings() {
		List<Setting> rtr = new ArrayList<>();
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
