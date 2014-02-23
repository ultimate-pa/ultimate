package de.uni_freiburg.informatik.ultimate.website.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.website.Setting;
import de.uni_freiburg.informatik.ultimate.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.website.Tool;
import de.uni_freiburg.informatik.ultimate.website.Toolchain;


public class BoogieLassoRankerTC extends Toolchain {

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.website.Toolchain#setDescription()
	 */
	@Override
	protected String setDescription() {
		return "Lasso Ranker toolchain";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setName()
	 */
	@Override
	protected String setName() {
		return "LassoRanker";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setId()
	 */
	@Override
	protected String setId() {
		return "boogieLassoRanker";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setTaskName()
	 */
	@Override
	protected TaskNames[] setTaskName() {
		return new TaskNames[] { TaskNames.RANK_SYNTHESIS_BOOGIE };
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
	
	
	/**
	 * List of tools required for LassoRanker on boogie code.
	 */
	static List<Tool> boogieTools() {
		List<Tool> tools = new ArrayList<Tool>();
		
		List<Setting> oPre = new ArrayList<Setting>();
		List<Setting> mPre = new ArrayList<Setting>();
		tools.add(new Tool(
				"de.uni_freiburg.informatik.ultimate.boogie.preprocessor",
				oPre, mPre, LoggingLevel.WARN));
		
		List<Setting> oRCFGB = new ArrayList<Setting>();
		List<Setting> mRCFGB = new ArrayList<Setting>();
        oRCFGB.add(new Setting(PrefStrings.s_RCFG_LABEL_ExternalSolver, Setting.SettingType.BOOLEAN,
        		PrefStrings.s_RCFG_LABEL_ExternalSolver, "false", false));
		mRCFGB.add(new Setting(PrefStrings.s_RCFG_LABEL_Simplify, Setting.SettingType.BOOLEAN,
				PrefStrings.s_RCFG_LABEL_Simplify, "true", false));
        oRCFGB.add(new Setting(PrefStrings.s_RCFG_LABEL_BlockSize, PrefStrings.s_RCFG_LABEL_BlockSize,
        		new String[] { PrefStrings.s_RCFG_VALUE_Block }, false, new String[] {
        		PrefStrings.s_RCFG_VALUE_Single, PrefStrings.s_RCFG_VALUE_Seq, PrefStrings.s_RCFG_VALUE_Block }, false));
		tools.add(new Tool("RCFGBuilder", oRCFGB, mRCFGB, LoggingLevel.WARN));
		
		List<Setting> oRank = new ArrayList<Setting>();
		List<Setting> mRank = new ArrayList<Setting>();
		tools.add(new Tool("LassoRanker", oRank, mRank,	LoggingLevel.WARN));
		oRank.add(new Setting(PrefStrings.s_LR_LABEL_use_external_solver, Setting.SettingType.BOOLEAN,
				PrefStrings.s_LR_LABEL_use_external_solver, "false", false));
		oRank.add(new Setting(PrefStrings.s_LR_LABEL_only_nondecreasing_invariants, Setting.SettingType.BOOLEAN,
				PrefStrings.s_LR_LABEL_only_nondecreasing_invariants, "true", false));
		oRank.add(new Setting(PrefStrings.s_LR_LABEL_nontermination_check_nonlinear, Setting.SettingType.BOOLEAN,
				PrefStrings.s_LR_LABEL_nontermination_check_nonlinear, "false", false));
		oRank.add(new Setting(PrefStrings.s_LR_LABEL_termination_check_nonlinear, Setting.SettingType.BOOLEAN,
				PrefStrings.s_LR_LABEL_termination_check_nonlinear, "false", false));
		mRank.add(new Setting(PrefStrings.s_LR_LABEL_nested_template_size, Setting.SettingType.INTEGER,
				PrefStrings.s_LR_LABEL_nested_template_size, "5", false));
		mRank.add(new Setting(PrefStrings.s_LR_LABEL_multiphase_template_size, Setting.SettingType.INTEGER,
				PrefStrings.s_LR_LABEL_multiphase_template_size, "5", false));
		mRank.add(new Setting(PrefStrings.s_LR_LABEL_lex_template_size, Setting.SettingType.INTEGER,
				PrefStrings.s_LR_LABEL_lex_template_size, "5", false));
		mRank.add(new Setting(PrefStrings.s_LR_LABEL_piecewise_template_size, Setting.SettingType.INTEGER,
				PrefStrings.s_LR_LABEL_piecewise_template_size, "5", false));
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
