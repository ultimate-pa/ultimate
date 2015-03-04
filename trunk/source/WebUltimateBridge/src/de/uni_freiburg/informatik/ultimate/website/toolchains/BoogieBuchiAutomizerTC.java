package de.uni_freiburg.informatik.ultimate.website.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.website.Setting;
import de.uni_freiburg.informatik.ultimate.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.website.Tool;
import de.uni_freiburg.informatik.ultimate.website.WebToolchain;


public class BoogieBuchiAutomizerTC extends WebToolchain {

	@Override
	protected String setDescription() {
		return "Büchi Automizer toolchain";
	}

	@Override
	protected String setName() {
		return "Büchi Automizer";
	}

	@Override
	protected String setId() {
		return "boogieBuchiAutomizer";
	}

	@Override
	protected TaskNames[] setTaskName() {
		return new TaskNames[] { TaskNames.TERMINATION_BOOGIE };
	}

    @Override
    protected String setLanguage() {
        return "boogie";
    }

    @Override
    protected String setUserInfo() {
        return null;
    }

	@Override
	protected List<Tool> setTools() {
		return boogieTools();
	}
	
	static List<Tool> boogieTools() {
		List<Tool> tools = new ArrayList<Tool>();
		
		tools.add(new Tool(PrefStrings.s_boogiePreprocessor));
		
		List<Setting> oRCFGB = new ArrayList<Setting>();
		List<Setting> mRCFGB = new ArrayList<Setting>();
        oRCFGB.add(new Setting(PrefStrings.s_RCFG_LABEL_Solver, PrefStrings.s_RCFG_LABEL_Solver,
        		new String[] { PrefStrings.s_RCFG_VALUE_SMTInterpol }, false, new String[] {
        		PrefStrings.s_RCFG_VALUE_SMTInterpol, PrefStrings.s_RCFG_VALUE_ExternalDefMo }, false));
        oRCFGB.add(new Setting(PrefStrings.s_RCFG_LABEL_BlockSize, PrefStrings.s_RCFG_LABEL_BlockSize,
        		new String[] { PrefStrings.s_RCFG_VALUE_Seq }, false, new String[] {
        		PrefStrings.s_RCFG_VALUE_Single, PrefStrings.s_RCFG_VALUE_Seq, PrefStrings.s_RCFG_VALUE_Block }, false));
		tools.add(new Tool(PrefStrings.s_rcfgBuilder, oRCFGB, mRCFGB, LoggingLevel.WARN));
		
		List<Setting> oBE = new ArrayList<Setting>();
		List<Setting> mBE = new ArrayList<Setting>();
		tools.add(new Tool(PrefStrings.s_blockencoding, oBE, mBE, LoggingLevel.WARN));
		oBE.add(new Setting(PrefStrings.s_BE_LABEL_CALLMINIMIZE, Setting.SettingType.BOOLEAN,
				PrefStrings.s_BE_LABEL_CALLMINIMIZE, "true", false));
		oBE.add(new Setting(PrefStrings.s_BE_LABEL_STRATEGY, PrefStrings.s_BE_LABEL_STRATEGY,
        		new String[] { PrefStrings.s_BE_VALUE_DisjunctiveRating }, false, new String[] {
				PrefStrings.s_BE_VALUE_DisjunctiveRating, PrefStrings.s_BE_VALUE_LargeBlock }, true));
		oBE.add(new Setting(PrefStrings.s_BE_LABEL_RATINGBOUND, Setting.SettingType.STRING,
				PrefStrings.s_BE_LABEL_RATINGBOUND, "0", false));
		
        
		List<Setting> oBA = new ArrayList<Setting>();
		List<Setting> mBA = new ArrayList<Setting>();
		oBA.add(new Setting(PrefStrings.s_TA_LABEL_Interpol, Setting.SettingType.STRING,
                "interpolation", PrefStrings.s_TA_VALUE_Forward, false));
		oBA.add(new Setting(PrefStrings.s_BA_LABEL_ExtSolverRank, Setting.SettingType.BOOLEAN,
				PrefStrings.s_BA_LABEL_ExtSolverRank, "false", false));
		oBA.add(new Setting(PrefStrings.s_BA_LABEL_Nonlinear, Setting.SettingType.BOOLEAN,
				"AllowNonlinearConstraints", "false", false));
		oBA.add(new Setting(PrefStrings.s_BA_LABEL_SimplifyTA, Setting.SettingType.BOOLEAN,
				PrefStrings.s_BA_LABEL_SimplifyTA, "true", false));
		tools.add(new Tool(PrefStrings.s_buchiautomizer, oBA, mBA, LoggingLevel.WARN));
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
