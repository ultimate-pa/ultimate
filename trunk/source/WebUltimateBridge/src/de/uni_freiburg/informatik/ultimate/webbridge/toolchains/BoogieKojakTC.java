package de.uni_freiburg.informatik.ultimate.webbridge.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tool;
import de.uni_freiburg.informatik.ultimate.webbridge.website.WebToolchain;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks.TaskNames;

/**
 * @author dietsch@informatik.uni-freiburg.de
 * @author nutz@informatik.uni-freiburg.de
 */
public class BoogieKojakTC extends WebToolchain {

	@Override
	protected String defineDescription() {
		return NameStrings.TOOL_KOJAK;
	}

	@Override
	protected String defineName() {
		return NameStrings.TOOL_KOJAK;
	}

	@Override
	protected String defineId() {
		return "boogieKojak";
	}

	@Override
	protected TaskNames[] defineTaskName() {
		return new TaskNames[] { TaskNames.KOJAK_BOOGIE };
	}

	@Override
	protected String defineLanguage() {
		return "boogie";
	}

	@Override
	protected List<Tool> defineTools() {
		final List<Tool> tools = new ArrayList<>();

		tools.add(new Tool(PrefStrings.s_boogiePreprocessor));
		tools.add(new Tool(PrefStrings.s_rcfgBuilder));
		tools.add(new Tool(PrefStrings.s_blockencoding));
		tools.add(new Tool(PrefStrings.s_codecheck));

		return tools;
	}

	@Override
	protected List<Setting> defineAdditionalSettings() {
		final List<Setting> rtr = new ArrayList<>();

		// rtr.add(new Setting(PrefStrings.s_CACSL_LABEL_StartFunction, SettingType.STRING, "Starting procedure: ",
		// "main", true));
		// rtr.add(new Setting(PrefStrings.s_CACSL_LABEL_TranslationMode, "Translation Mode",
		// new String[] { PrefStrings.s_CACSL_VALUE_Svcomp }, false, new String[] {
		// PrefStrings.s_CACSL_VALUE_Base, PrefStrings.s_CACSL_VALUE_Svcomp }, true));

		return rtr;
	}

	@Override
	protected String defineToolchainSettingsFile() {
		return "Kojak.epf";
	}

}
