package de.uni_freiburg.informatik.ultimate.website.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.website.Setting;
import de.uni_freiburg.informatik.ultimate.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.website.Tool;
import de.uni_freiburg.informatik.ultimate.website.WebToolchain;

public class CLassoRankerTC extends WebToolchain {

	@Override
	protected String setDescription() {
		return "Lasso Ranker toolchain";
	}

	@Override
	protected String setName() {
		return "LassoRanker";
	}

	@Override
	protected String setId() {
		return "cLassoRanker";
	}

	@Override
	protected TaskNames[] setTaskName() {
		return new TaskNames[] { TaskNames.RANK_SYNTHESIS_C };
	}

	@Override
	protected List<Tool> setTools() {
		List<Tool> tools = new ArrayList<Tool>();
		List<Setting> oCACSL = new ArrayList<Setting>();
		// oCACSL.add(new Setting("/CheckedMethod", Setting.SettingType.STRING,
		// "Checked Method: ", "main", true));
		List<Setting> mCACSL = new ArrayList<Setting>();
		tools.add(new Tool(PrefStrings.s_cacsl2boogietranslator, oCACSL, mCACSL, LoggingLevel.WARN));
		tools.addAll(BoogieLassoRankerTC.boogieTools());
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
