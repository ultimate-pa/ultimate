package de.uni_freiburg.informatik.ultimate.website.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.website.Setting;
import de.uni_freiburg.informatik.ultimate.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.website.WebToolchain.LoggingLevel;
import de.uni_freiburg.informatik.ultimate.website.Tool;
import de.uni_freiburg.informatik.ultimate.website.WebToolchain;


public class BoogieBuchiAutomizerTC extends WebToolchain {

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.website.Toolchain#setDescription()
	 */
	@Override
	protected String setDescription() {
		return "Büchi Automizer toolchain";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setName()
	 */
	@Override
	protected String setName() {
		return "BüchiAutomizer";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setId()
	 */
	@Override
	protected String setId() {
		return "boogieBuchiAutomizer";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setTaskName()
	 */
	@Override
	protected TaskNames[] setTaskName() {
		return new TaskNames[] { TaskNames.TERMINATION_BOOGIE };
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setTools()
	 */
	@Override
	protected List<Tool> setTools() {
		return boogieTools();
	}
	
	static List<Tool> boogieTools() {
		List<Tool> tools = new ArrayList<Tool>();
		
		List<Setting> oPre = new ArrayList<Setting>();
		List<Setting> mPre = new ArrayList<Setting>();
		tools.add(new Tool(
				"de.uni_freiburg.informatik.ultimate.boogie.preprocessor",
				oPre, mPre, LoggingLevel.WARN));
		
		List<Setting> oRCFGB = new ArrayList<Setting>();
		List<Setting> mRCFGB = new ArrayList<Setting>();
		tools.add(new Tool("RCFGBuilder", oRCFGB, mRCFGB, LoggingLevel.WARN));
        oRCFGB.add(new Setting(PrefStrings.s_RCFG_LABEL_ExternalSolver, Setting.SettingType.BOOLEAN,
        		PrefStrings.s_RCFG_LABEL_ExternalSolver, "false", false));
        oRCFGB.add(new Setting(PrefStrings.s_RCFG_LABEL_BlockSize, PrefStrings.s_RCFG_LABEL_BlockSize,
        		new String[] { PrefStrings.s_RCFG_VALUE_Seq }, false, new String[] {
        		PrefStrings.s_RCFG_VALUE_Single, PrefStrings.s_RCFG_VALUE_Seq, PrefStrings.s_RCFG_VALUE_Block }, false));
        
		List<Setting> oBE = new ArrayList<Setting>();
		List<Setting> mBE = new ArrayList<Setting>();
		tools.add(new Tool("BlockEncoding", oBE, mBE, LoggingLevel.WARN));
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
		tools.add(new Tool("BuchiAutomizer", oBA, mBA, LoggingLevel.WARN));
		return tools;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.website.Toolchain#setPluginsLoggingLevel
	 * ()
	 */
	@Override
	protected LoggingLevel setPluginsLoggingLevel() {
		return LoggingLevel.INFO;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.website.Toolchain#setToolsLoggingLevel
	 * ()
	 */
	@Override
	protected LoggingLevel setToolsLoggingLevel() {
		return LoggingLevel.INFO;
	}
}
