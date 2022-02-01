package de.uni_freiburg.informatik.ultimate.webbridge.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting.SettingType;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tool;
import de.uni_freiburg.informatik.ultimate.webbridge.website.WebToolchain;

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
		final List<Tool> rtr = new ArrayList<>();

		rtr.add(new Tool(PrefStrings.SYNTAXCHECKER));
		rtr.add(new Tool(PrefStrings.CACSL2BOOGIETRANSLATOR));
		rtr.add(new Tool(PrefStrings.BOOGIE_PREPROCESSOR));
		rtr.add(new Tool(PrefStrings.RCFGBUILDER));
		rtr.add(new Tool(PrefStrings.TRACE_ABSTRACTION));
		rtr.add(new Tool(PrefStrings.LTL2AUT));
		rtr.add(new Tool(PrefStrings.BUCHIPROGRAMPRODUCT));
		rtr.add(new Tool(PrefStrings.BLOCKENCODING));
		rtr.add(new Tool(PrefStrings.BUCHIAUTOMIZER));

		return rtr;
	}

	@Override
	protected List<Setting> defineAdditionalSettings() {
		final List<Setting> rtr = new ArrayList<>();

		rtr.add(new Setting(PrefStrings.CACSL_LABEL_StartFunction, SettingType.STRING, "Starting procedure: ", "main",
				true));
		rtr.add(new Setting(PrefStrings.TA_LABEL_HOARE, Setting.SettingType.BOOLEAN, "Compute Hoare Annotation",
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
