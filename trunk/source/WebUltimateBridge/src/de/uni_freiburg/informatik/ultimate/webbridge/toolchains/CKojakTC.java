package de.uni_freiburg.informatik.ultimate.webbridge.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tool;
import de.uni_freiburg.informatik.ultimate.webbridge.website.WebToolchain;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks.TaskNames;

/**
 * @author dietsch@informatik.uni-freiburg.de
 */
public class CKojakTC extends WebToolchain {

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
		return "cKojak";
	}

	@Override
	protected TaskNames[] defineTaskName() {
		return new TaskNames[] { TaskNames.KOJAK_C };
	}

	@Override
	protected String defineLanguage() {
		return "c";
	}

	@Override
	protected List<Tool> defineTools() {
		final List<Tool> tools = new ArrayList<>();

		tools.add(new Tool(PrefStrings.SYNTAXCHECKER));
		tools.add(new Tool(PrefStrings.CACSL2BOOGIETRANSLATOR));
		tools.add(new Tool(PrefStrings.BOOGIE_PREPROCESSOR));
		tools.add(new Tool(PrefStrings.RCFGBUILDER));
		tools.add(new Tool(PrefStrings.BLOCKENCODING));
		tools.add(new Tool(PrefStrings.CODECHECK));

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
