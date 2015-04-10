package de.uni_freiburg.informatik.ultimate.website.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.website.Setting.SettingType;
import de.uni_freiburg.informatik.ultimate.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.website.Setting;
import de.uni_freiburg.informatik.ultimate.website.Tool;
import de.uni_freiburg.informatik.ultimate.website.WebToolchain;

public class CLassoRankerTC extends WebToolchain {

	@Override
	protected String defineDescription() {
		return "Lasso Ranker toolchain";
	}

	@Override
	protected String defineName() {
		return "Lasso Ranker";
	}

	@Override
	protected String defineId() {
		return "cLassoRanker";
	}

	@Override
	protected TaskNames[] defineTaskName() {
		return new TaskNames[] { TaskNames.RANK_SYNTHESIS_C };
	}

    @Override
    protected String defineLanguage() {
        return "c";
    }

	@Override
	protected List<Tool> defineTools() {
		List<Tool> tools = new ArrayList<Tool>();
		
		tools.add(new Tool(PrefStrings.s_cacsl2boogietranslator));
		tools.addAll(BoogieLassoRankerTC.boogieLassoRankerToolchain());

		return tools;
	}
	
	@Override
	protected List<Setting> defineAdditionalSettings() {
		List<Setting> rtr = BoogieLassoRankerTC.boogieLassoRankerAdditionalSettings();
//		rtr.add(new Setting(PrefStrings.s_CACSL_LABEL_StartFunction, SettingType.STRING, "Starting procedure: ",
//				"main", true));
		return rtr;
	}
	
	@Override
	protected String defineToolchainSettingsFile() {
		return "LassoRanker.epf";
	}

}
