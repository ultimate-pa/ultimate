package de.uni_freiburg.informatik.ultimate.website.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.website.Setting;
import de.uni_freiburg.informatik.ultimate.website.Setting.SettingType;
import de.uni_freiburg.informatik.ultimate.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.website.Tool;
import de.uni_freiburg.informatik.ultimate.website.WebToolchain;

public class CLTLAutomizerTC extends WebToolchain {

	@Override
	protected String defineDescription() {
		return "LTL Automizer toolchain";
	}

	@Override
	protected String defineName() {
		return "LTL Automizer";
	}

	@Override
	protected String defineId() {
		return "cLTLAutomizer";
	}

	@Override
	protected TaskNames[] defineTaskName() {
		return new TaskNames[] { TaskNames.LTLAUTOMIZER_C };
	}

	@Override
	protected String defineLanguage() {
		return "c";
	}

	@Override
	protected String defineUserInfo() {
		return "Note: The timeout is set to 150s";
	}

	@Override
	protected List<Tool> defineTools() {
		List<Tool> rtr = new ArrayList<Tool>();

		rtr.add(new Tool(PrefStrings.s_cacsl2boogietranslator));
		rtr.add(new Tool(PrefStrings.s_boogiePreprocessor));
		rtr.add(new Tool(PrefStrings.s_rcfgBuilder));
		rtr.add(new Tool(PrefStrings.s_traceAbstraction));
		rtr.add(new Tool(PrefStrings.s_ltl2aut));
		rtr.add(new Tool(PrefStrings.s_buchiProgramProduct));
		rtr.add(new Tool(PrefStrings.s_buchiautomizer));

		return rtr;
	}

	@Override
	protected List<Setting> defineAdditionalSettings() {
		List<Setting> rtr = new ArrayList<Setting>();

		rtr.add(new Setting(PrefStrings.s_CACSL_LABEL_StartFunction, SettingType.STRING, "Starting procedure: ",
				"main", true));
		rtr.add(new Setting(PrefStrings.s_TA_LABEL_Hoare, Setting.SettingType.BOOLEAN, "Compute Hoare Annotation",
				"true", true));

		return rtr;
	}

	@Override
	public long getTimeout() {
		return 150 * 1000;
	}

	@Override
	protected String defineToolchainSettingsFile() {
		return "LTLAutomizerC-Default.epf";
	}
}
