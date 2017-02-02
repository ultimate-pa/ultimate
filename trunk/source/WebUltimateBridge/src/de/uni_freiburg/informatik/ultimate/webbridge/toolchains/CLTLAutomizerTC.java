package de.uni_freiburg.informatik.ultimate.webbridge.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tool;
import de.uni_freiburg.informatik.ultimate.webbridge.website.WebToolchain;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting.SettingType;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks.TaskNames;

/**
 * @author dietsch@informatik.uni-freiburg.de
 */
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
		return "c_cpp";
	}

	@Override
	protected String defineUserInfo() {
		return "Note: The timeout is set to 150s";
	}

	@Override
	protected List<Tool> defineTools() {
		final List<Tool> rtr = new ArrayList<Tool>();

		rtr.add(new Tool(PrefStrings.s_syntaxchecker));
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
		final List<Setting> rtr = new ArrayList<Setting>();

		rtr.add(new Setting(PrefStrings.s_CACSL_LABEL_StartFunction, SettingType.STRING, "Starting procedure: ",
				"main", true));
		rtr.add(new Setting(PrefStrings.s_TA_LABEL_Hoare, Setting.SettingType.BOOLEAN, "Compute Hoare Annotation",
				"true", true));

		return rtr;
	}

	@Override
	public long getTimeout() {
		return 15 * 60 * 1000;
	}

	@Override
	protected String defineToolchainSettingsFile() {
		return "LTLAutomizerC-Default.epf";
	}
}
