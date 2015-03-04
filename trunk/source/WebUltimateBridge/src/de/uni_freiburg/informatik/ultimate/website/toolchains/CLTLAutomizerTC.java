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
	protected String setDescription() {
		return "LTL Automizer toolchain";
	}

	@Override
	protected String setName() {
		return "LTL Automizer";
	}

	@Override
	protected String setId() {
		return "cLTLAutomizer";
	}

	@Override
	protected TaskNames[] setTaskName() {
		return new TaskNames[] { TaskNames.VerifyC };
	}

    @Override
    protected String setLanguage() {
        return "c";
    }

    @Override
    protected String setUserInfo() {
        return "This webinterface is currently under construction and does not work!";
    }

	@Override
	protected List<Tool> setTools() {
		List<Tool> tools = new ArrayList<Tool>();
		List<Setting> oCACSL = new ArrayList<Setting>();
		oCACSL.add(new Setting(PrefStrings.s_CACSL_LABEL_StartFunction, SettingType.STRING,
				"Starting procedure: ", "main", true));
		List<Setting> mCACSL = new ArrayList<Setting>();
		tools.add(new Tool(PrefStrings.s_cacsl2boogietranslator, oCACSL, mCACSL,
				LoggingLevel.WARN));

		tools.addAll(BoogieBuchiAutomizerTC.boogieTools());
		return tools;
	}

	@Override
	protected LoggingLevel setPluginsLoggingLevel() {
		return LoggingLevel.INFO;
	}

	@Override
	protected LoggingLevel setToolsLoggingLevel() {
		return LoggingLevel.INFO;
	}
}
